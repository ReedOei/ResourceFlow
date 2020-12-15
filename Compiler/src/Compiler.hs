{-# LANGUAGE TemplateHaskell #-}

module Compiler where

import Control.Lens
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map

import AST

data Env = Env { _freshCounter :: Integer,
                 _typeEnv :: Map String BaseType,
                 _declarations :: Map String Decl,
                 _solDecls :: Map String SolDecl }
    deriving (Show, Eq)
makeLenses ''Env

newEnv = Env { _freshCounter = 0,
               _typeEnv = Map.empty,
               _declarations = Map.empty,
               _solDecls = Map.empty }

freshName :: State Env String
freshName = do
    i <- freshCounter <<+= 1
    pure $ "v" ++ show i

freshVar :: State Env Locator
freshVar = Var <$> freshName

typeOf :: String -> State Env BaseType
typeOf x = do
    maybeT <- Map.lookup x . view typeEnv <$> get
    case maybeT of
        Nothing -> error $ "Tried to lookup variable " ++ x ++ " in the type environment; not found!"
        Just t -> pure t

modifiers :: String -> State Env [Modifier]
modifiers typeName = do
    decl <- Map.lookup typeName . view declarations <$> get
    case decl of
        Nothing -> error $ "Tried to lookup type declaration " ++ typeName ++ "; not found!"
        Just tx@TransformerDecl{} -> error $ "Tried to lookup type declaration " ++ typeName ++ "; but got: " ++ show tx
        Just (TypeDecl _ mods _) -> pure mods

buildExpr :: Locator -> State Env SolExpr
buildExpr (Var s) = pure $ SolVar s
buildExpr l = error $ "Unsupported locator: " ++ show l

compileProg :: Program -> State Env Contract
compileProg (Program decls mainBody) = do
    mapM_ compileDecl decls
    stmts <- concat <$> mapM compileStmt mainBody
    pure $ Contract "0.7.5" "C" [ Constructor [] stmts ]

compileDecl :: Decl -> State Env ()
compileDecl decl@(TypeDecl name ms baseT) = do
    modify $ over declarations $ Map.insert name decl
compileDecl d = error $ "compileDecl not implemented for: " ++ show d

compileStmt :: Stmt -> State Env [SolStmt]
compileStmt (Flow src dst) = do
    (srcLoc, srcComp) <- locate src
    (dstLoc, dstComp) <- locate dst
    transfer <- lookupValue (\orig val -> receiveValue orig val dstLoc) srcLoc

    pure $ srcComp ++ dstComp ++ transfer

compileStmt (FlowTransform src transformer dst) = error "unimplemented!"

locate :: Locator -> State Env (Locator, [SolStmt])
locate (NewVar x t) = do
    modify $ over typeEnv (Map.insert x t)
    decl <- declareVar x t
    pure (Var x, [SolVarDef decl])
locate l = pure (l, [])

lookupValue :: (SolExpr -> SolExpr -> State Env [SolStmt]) -> Locator -> State Env [SolStmt]
lookupValue f (IntConst i) = f (SolInt i) (SolInt i)
lookupValue f (Var x) = do
    t <- typeOf x
    case t of
        Nat -> f (SolVar x) (SolVar x)
        PsaBool -> f (SolVar x) (SolVar x)
        PsaString -> f (SolVar x) (SolVar x)
        Address -> f (SolVar x) (SolVar x)
        Table [] _ -> do
            idxVarName <- freshName
            let idxVar = SolVar idxVarName

            body <- f (SolIdx (SolVar x) idxVar) (SolIdx (SolVar x) idxVar)

            pure [ For (SolVarDefInit (SolVarDecl (SolTypeName "uint") idxVarName) (SolInt 0))
                       (SolLt idxVar (FieldAccess (SolVar x) "length"))
                       (SolPostInc idxVar)
                       body ]
        _ -> error "Not implemented!"
lookupValue f (Multiset t elems) = concat <$> mapM (lookupValue f) elems

receiveValue :: SolExpr -> SolExpr -> Locator -> State Env [SolStmt]
receiveValue orig src (Var x) = do
    t <- typeOf x
    demotedT <- demoteBaseType t
    tIsFungible <- isFungible t

    main <-
        case demotedT of
            Nat | tIsFungible -> pure [ SolAssign (SolVar x) (SolAdd (SolVar x) src) ]

            Table [] _ ->
                pure [ ExprStmt (SolCall (FieldAccess (SolVar x) "push") [ src ] ) ]

            _ -> error "Not implemented!"

    let cleanup = if isPrimitiveExpr orig then [] else [ Delete orig ]

    pure $ main ++ cleanup

receiveValue orig src dst = error $ "Cannot receive values in destination: " ++ show dst

declareVar :: String -> BaseType -> State Env SolVarDecl
declareVar x t = do
    demotedT <- demoteBaseType t
    if isPrimitive demotedT then
        pure $ SolVarDecl (toSolType t) x
    else
        -- TODO: Might need to change this so it's not always memory...
        pure $ SolVarLocDecl (toSolType t) Memory x

isPrimitiveExpr :: SolExpr -> Bool
isPrimitiveExpr (SolInt _) = True
isPrimitiveExpr (SolBool _) = True
isPrimitiveExpr (SolStr _) = True
isPrimitiveExpr (SolAddr _) = True
isPrimitiveExpr _ = False

isPrimitive :: BaseType -> Bool
isPrimitive Nat = True
isPrimitive PsaBool = True
isPrimitive PsaString = True
isPrimitive Address = True
isPrimitive _ = False

isFungible :: BaseType -> State Env Bool
isFungible Nat = pure True
isFungible (Named t) = (Fungible `elem`) <$> modifiers t
-- TODO: Update this for later, because tables should be fungible too?
isFungible _ = pure False

toSolType :: BaseType -> SolType
toSolType Nat = SolTypeName "uint"
toSolType PsaBool = SolTypeName "bool"
toSolType PsaString = SolTypeName "string"
toSolType Address = SolTypeName "address"
toSolType (Table [] (_, t)) = SolArray $ toSolType t

demoteBaseType :: BaseType -> State Env BaseType
demoteBaseType Nat = pure Nat
demoteBaseType PsaBool = pure PsaBool
demoteBaseType PsaString = pure PsaString
demoteBaseType Address = pure Address
demoteBaseType (Table keys (q, t)) = Table keys . (q,) <$> demoteBaseType t
demoteBaseType t = error $ "demoteBaseType called with " ++ show t
