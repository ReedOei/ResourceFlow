{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Transform where

import Control.Lens
import Control.Monad.State

import AST
import Env
import Phase

-- | Applies functions accross to (result, Env) pairs across phases
(>>>) :: (ProgramTransform p1 p2, PhaseTransition p1 p1) => (a, Env p1) -> (a -> State (Env p2) b) -> (b, Env p2)
(a, s) >>> f = runState (f a) (transformEnv s)

-- AST transforms
class (Phase a, Phase b) => ProgramTransform a b where
    transformXType :: (Phase c, PhaseTransition a c) => XType a -> State (Env c) (XType b)

transformBaseType :: forall a b c. (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => BaseType a -> State (Env c) (BaseType b)
transformBaseType Nat = pure Nat
transformBaseType PsaBool = pure PsaBool
transformBaseType PsaString = pure PsaString
transformBaseType Address = pure Address
transformBaseType (Named name) = pure $ Named name
transformBaseType Bot = pure Bot

transformBaseType (Record keys fields) = Record keys <$> mapM transformVarDef fields
transformBaseType (Table keys t) = Table keys <$> transformXType @a @b @c t

transformQuantifiedType :: forall a b c. (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => QuantifiedType a -> State (Env c) (QuantifiedType b)
transformQuantifiedType (q, t) = (q,) <$> transformBaseType t

transformVarDef :: forall a b c. (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => VarDef a -> State (Env c) (VarDef b)
transformVarDef (VarDef name t) = VarDef name <$> transformXType @a @b t

transformLocator :: forall a b c. (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => Locator a -> State (Env c) (Locator b)
transformLocator (IntConst i) = pure $ IntConst i
transformLocator (BoolConst b) = pure $ BoolConst b
transformLocator (StrConst s) = pure $ StrConst s
transformLocator (AddrConst addr) = pure $ AddrConst addr
transformLocator (Var var) = pure $ Var var
transformLocator (Field l name) = flip Field name <$> transformLocator l

transformLocator (Multiset t locators) = Multiset <$> transformXType @a @b t <*> mapM transformLocator locators

transformLocator (NewVar name baseT) = NewVar name <$> transformBaseType baseT
transformLocator Consume = pure Consume

transformLocator (RecordLit keys members) = do
    let (varDefs, locators) = unzip members
    transformedVarDefs <- mapM transformVarDef varDefs
    transformedLocators <- mapM transformLocator locators
    pure $ RecordLit keys (zip transformedVarDefs transformedLocators)

transformLocator (Filter l q predName args) = do
    transformedL <- transformLocator l
    Filter transformedL q predName <$> mapM transformLocator args

transformLocator (Select l k) = Select <$> transformLocator l <*> transformLocator k

transformTransformer :: (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => Transformer a -> State (Env c) (Transformer b)
transformTransformer (Construct name args) = Construct name <$> mapM transformLocator args
transformTransformer (Call name args) = Call name <$> mapM transformLocator args

transformPrecondition :: (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => Precondition a -> State (Env c) (Precondition b)
transformPrecondition (Conj conds) = Conj <$> mapM transformPrecondition conds
transformPrecondition (Disj conds) = Disj <$> mapM transformPrecondition conds

transformPrecondition (BinOp op a b) = BinOp op <$> transformLocator a <*> transformLocator b

transformPrecondition (NegateCond cond) = NegateCond <$> transformPrecondition cond

transformStmt :: forall a b c. (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => Stmt a -> State (Env c) (Stmt b)
transformStmt (Flow src dst) = Flow <$> transformLocator src <*> transformLocator dst

transformStmt (FlowTransform src transformer dst) = FlowTransform <$> transformLocator src <*> transformTransformer transformer <*> transformLocator dst

transformStmt (OnlyWhen precondition) = OnlyWhen <$> transformPrecondition precondition

transformStmt (Try checkC1 checkCs) = Try <$> mapM transformStmt checkC1 <*> mapM transformStmt checkCs

transformStmt Revert = pure Revert

transformDecl :: (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => Decl a -> State (Env c) (Decl b)
transformDecl (TypeDecl s modifiers baseT) = TypeDecl s modifiers <$> transformBaseType baseT

transformDecl (TransformerDecl name args ret body) = TransformerDecl name <$> mapM transformVarDef args <*> transformVarDef ret <*> mapM transformStmt body

transformEnv :: forall a b. (Phase a, Phase b, ProgramTransform a b, PhaseTransition a a) => Env a -> Env b
transformEnv env = let (transformedTypeEnvs, s) = runState (mapM transformBaseType $ env^.typeEnv) env
                       (transformedDecls, _) = runState (mapM transformDecl $ env^.declarations) env
                   in Env { _freshCounter = env^.freshCounter,
                            _typeEnv = transformedTypeEnvs,
                            _declarations = transformedDecls,
                            _solDecls = env^.solDecls,
                            _allocators = env^.allocators,
                            _errors = env^.errors,
                            _phaseMarker = promotePhase $ env^.phaseMarker }
    where
        promotePhase Preprocessor = Typechecker
        promotePhase Typechecker  = Compiler
        promotePhase Compiler     = Compiler
