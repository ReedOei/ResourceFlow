{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module AST where

import Data.Char (toLower)
import Data.List (intercalate)

import Phase

data Modifier = Fungible | Immutable | Consumable | Asset | Unique
    deriving (Show, Eq)

data TyQuant = Empty | Any | One | Nonempty
    deriving (Show, Eq)

class DefinesXType p where
    type XType p    :: *
    extractBaseType :: XType p -> BaseType p
    replaceBaseType :: XType p -> BaseType p -> XType p
    bot :: XType p

instance DefinesXType Preprocessing where
    type XType Preprocessing = InferrableType Preprocessing

    extractBaseType (Complete (q, t)) = t
    extractBaseType (Infer t) = t

    replaceBaseType (Complete (q, _)) t = Complete (q, t)
    replaceBaseType (Infer _) t = Infer t

    bot = Complete (Any, Bot)

instance DefinesXType Typechecking where
    type XType Typechecking = QuantifiedType Typechecking
    extractBaseType (q, t) = t
    replaceBaseType (q, _) t = (q, t)
    bot = (Any, Bot)

instance DefinesXType Compiling where
    type XType Compiling = QuantifiedType Compiling
    extractBaseType (q, t) = t
    replaceBaseType (q, _) t = (q, t)
    bot = (Any, Bot)

-- AST types, parameterized by compiler phase
data BaseType phase = Nat | PsaBool | PsaString | Address
                    | Record [String] [VarDef phase]
                    | Table [String] (XType phase)
                    | Named String
                    | Bot

type QuantifiedType phase = (TyQuant, BaseType phase)

data InferrableType phase = Complete (QuantifiedType phase)
                          | Infer (BaseType phase)
                          | InferredType

data VarDef phase = VarDef String (XType phase)

data Locator phase = IntConst Integer
                   | BoolConst Bool
                   | StrConst String
                   | AddrConst String
                   | Var String
                   | Field (Locator phase) String
                   | Multiset (XType phase) [Locator phase]
                   | NewVar String (BaseType phase)
                   | Consume
                   | RecordLit [String] [(VarDef phase, Locator phase)]
                   | Filter (Locator phase) TyQuant String [Locator phase]
                   | Select (Locator phase) (Locator phase)

data Transformer phase = Call String [Locator phase]
                       | Construct String [Locator phase]

data Op = OpLt | OpGt | OpLe | OpGe | OpEq | OpNe | OpIn | OpNotIn
    deriving (Show, Eq)

data Precondition phase = Conj [Precondition phase]
                        | Disj [Precondition phase]
                        | BinOp Op (Locator phase) (Locator phase)
                        | NegateCond (Precondition phase)

data Stmt phase = Flow (Locator phase) (Locator phase)
                | FlowTransform (Locator phase) (Transformer phase) (Locator phase)
                | OnlyWhen (Precondition phase)
                | Revert
                | Try [Stmt phase] [Stmt phase]

data Decl phase = TypeDecl String [Modifier] (BaseType phase)
                | TransformerDecl String [VarDef phase] (VarDef phase) [Stmt phase]

data Program phase = Program [Decl phase] [Stmt phase]

-- Solidity stuff
data DataLoc = Memory | Calldata | Storage
    deriving (Show, Eq)

data SolType = SolTypeName String
             | SolArray SolType
             | SolMapping SolType SolType
    deriving (Show, Eq, Ord)

data SolVarDecl = SolVarLocDecl SolType DataLoc String
                | SolVarDecl SolType String
    deriving (Show, Eq)

data SolExpr = SolBool Bool
             | SolInt Integer
             | SolAddr String
             | SolStr String
             | SolVar String
             | FieldAccess SolExpr String
             | SolPostInc SolExpr
             | SolNot SolExpr
             | SolCall SolExpr [SolExpr]
             | SolIdx SolExpr SolExpr
             | SolAdd SolExpr SolExpr
             | SolSub SolExpr SolExpr
             | SolOr SolExpr SolExpr
             | SolLt SolExpr SolExpr
             | SolLte SolExpr SolExpr
             | SolEq SolExpr SolExpr
    deriving (Show, Eq)

data SolStmt = ExprStmt SolExpr
             | SolVarDefInit SolVarDecl SolExpr
             | SolVarDef SolVarDecl
             | SolAssign SolExpr SolExpr
             | Delete SolExpr
             | For SolStmt SolExpr SolExpr [SolStmt]
             | SolTry SolExpr [SolVarDecl] [SolStmt] [SolStmt]
             | If SolExpr [SolStmt]
             | IfElse SolExpr [SolStmt] [SolStmt]
             | SolRevert SolExpr
             | Require SolExpr SolExpr
    deriving (Show, Eq)

data Visibility = Public | Private | Internal | External
    deriving (Show, Eq)

data SolDecl = Struct String [SolVarDecl]
             | Function String [SolVarDecl] Visibility [SolVarDecl] [SolStmt]
             | Constructor [SolVarDecl] [SolStmt]
             | FieldDef SolVarDecl
    deriving (Show, Eq)

data Contract = Contract String String [SolDecl]
    deriving (Show, Eq)

deriving instance Eq (XType phase) => Eq (BaseType phase)
deriving instance Eq (XType phase) => Eq (InferrableType phase)
deriving instance Eq (XType phase) => Eq (VarDef phase)
deriving instance Eq (XType phase) => Eq (Locator phase)
deriving instance Eq (XType phase) => Eq (Transformer phase)
deriving instance Eq (XType phase) => Eq (Precondition phase)
deriving instance Eq (XType phase) => Eq (Stmt phase)
deriving instance Eq (XType phase) => Eq (Decl phase)
deriving instance Eq (XType phase) => Eq (Program phase)

deriving instance Show (XType phase) => Show (BaseType phase)
deriving instance Show (XType phase) => Show (InferrableType phase)
deriving instance Show (XType phase) => Show (VarDef phase)
deriving instance Show (XType phase) => Show (Locator phase)
deriving instance Show (XType phase) => Show (Transformer phase)
deriving instance Show (XType phase) => Show (Precondition phase)
deriving instance Show (XType phase) => Show (Stmt phase)
deriving instance Show (XType phase) => Show (Decl phase)
deriving instance Show (XType phase) => Show (Program phase)

-- PrettyPrint definitions for all the AST types
class PrettyPrint a where
    prettyPrint :: a -> [String]

    prettyStr :: a -> String
    prettyStr = intercalate "\n" . prettyPrint

indent = ("    "++)

instance PrettyPrint (XType phase) => PrettyPrint (Locator phase) where
    prettyPrint (IntConst i) = [show i]
    prettyPrint (BoolConst b) = [ map toLower $ show b ]
    prettyPrint (StrConst s) = [ show s ]
    prettyPrint (AddrConst s) = [s]
    prettyPrint (Var x) = [x]
    prettyPrint (Field l x) = [ prettyStr l ++ "." ++ x]
    prettyPrint (Multiset t elems) = [ "[ " ++ prettyStr t ++ " ; " ++ intercalate ", " (map prettyStr elems) ++ " ]" ]
    prettyPrint (NewVar x t) = [ "var " ++ x ++ " : " ++ prettyStr t ]
    prettyPrint Consume = ["consume"]
    prettyPrint (Filter l q f args) = [ prettyStr l ++ "[ " ++ prettyStr q ++ " such that " ++ f ++ "(" ++ intercalate ", " (map prettyStr args) ++ ") ]" ]
    prettyPrint (Select l k) = [ prettyStr l ++ "[" ++ prettyStr k ++ "]" ]
    prettyPrint (RecordLit keys fields) = [ "record(" ++ intercalate ", " keys ++ ") {" ++ intercalate ", " (map (\(x, t) -> prettyStr x ++ " |-> " ++ prettyStr t) fields) ]

instance PrettyPrint (XType phase) => PrettyPrint (Transformer phase) where
    prettyPrint (Call name args) = [ name ++ "(" ++ intercalate ", " (map prettyStr args) ++ ")" ]
    prettyPrint (Construct name args) = [ "new " ++ name ++ "(" ++ intercalate ", " (map prettyStr args) ++ ")" ]

instance PrettyPrint Op where
    prettyPrint OpLt = ["<"]
    prettyPrint OpGt = [">"]
    prettyPrint OpLe = ["<="]
    prettyPrint OpGe = [">="]
    prettyPrint OpEq = ["="]
    prettyPrint OpNe = ["!="]
    prettyPrint OpIn = ["in"]
    prettyPrint OpNotIn = ["not in"]

instance PrettyPrint (XType phase) => PrettyPrint (Precondition phase) where
    prettyPrint (Conj conds) = [ intercalate " and " (map (\cond -> "(" ++ prettyStr cond ++ ")") conds) ]
    prettyPrint (Disj conds) = [ intercalate " or " (map (\cond -> "(" ++ prettyStr cond ++ ")") conds) ]
    prettyPrint (BinOp op a b) = [ prettyStr a ++ " " ++ prettyStr op ++ " " ++ prettyStr b ]
    prettyPrint (NegateCond cond) = [ "!(" ++ prettyStr cond ++ ")" ]

instance PrettyPrint (XType phase) => PrettyPrint (Stmt phase) where
    prettyPrint (Flow src dst) = [ prettyStr src ++ " --> " ++ prettyStr dst ]
    prettyPrint (FlowTransform src transformer dst) = [ prettyStr src ++ " --> " ++ prettyStr transformer ++ " --> " ++ prettyStr dst ]
    prettyPrint (Try tryBlock catchBlock) =
        [ "try {" ]
        ++ concatMap (map indent . prettyPrint) tryBlock
        ++ [ "} catch { " ]
        ++ concatMap (map indent . prettyPrint) catchBlock
        ++ [ "}" ]
    prettyPrint (OnlyWhen cond) = [ "only when " ++ prettyStr cond ]
    prettyPrint Revert = [ "revert" ]

instance PrettyPrint Modifier where
    prettyPrint Fungible = ["fungible"]
    prettyPrint Asset = ["asset"]
    prettyPrint Immutable = ["immutable"]
    prettyPrint Unique = ["unique"]
    prettyPrint Consumable = ["consumable"]

instance PrettyPrint TyQuant where
    prettyPrint Empty = ["empty"]
    prettyPrint Any = ["any"]
    prettyPrint One = ["one"]
    prettyPrint Nonempty = ["nonempty"]

instance PrettyPrint (XType phase) => PrettyPrint (QuantifiedType phase) where
    prettyPrint (q,t) = [ prettyStr q ++ " " ++ prettyStr t ]

instance PrettyPrint (XType phase) => PrettyPrint (InferrableType phase) where
    prettyPrint (Complete qt) = prettyPrint qt
    prettyPrint (Infer baseT) = ["infer " ++ prettyStr baseT]
    prettyPrint InferredType = ["inferred"]

instance PrettyPrint (XType phase) => PrettyPrint (VarDef phase) where
    prettyPrint (VarDef x t) = [ x ++ " : " ++ prettyStr t ]

instance PrettyPrint (XType phase) => PrettyPrint (BaseType phase) where
    prettyPrint Nat = ["nat"]
    prettyPrint PsaBool = ["bool"]
    prettyPrint PsaString = ["string"]
    prettyPrint Address = ["address"]
    prettyPrint (Named t) = [t]
    prettyPrint (Table keys t) = [ "table(" ++ intercalate ", " keys ++ ") " ++ prettyStr t ]
    prettyPrint (Record keys fields) = [ "record(" ++ intercalate ", " keys ++ ") {" ++ intercalate ", " (map prettyStr fields) ++ "}" ]
    prettyPrint Bot = ["⊥"]

instance PrettyPrint (XType phase) => PrettyPrint (Decl phase) where
    prettyPrint (TypeDecl name ms baseT) =
        [ "type " ++ name ++ " is " ++ unwords (map prettyStr ms) ++ " " ++ prettyStr baseT ]
    prettyPrint (TransformerDecl name args ret body) =
        [ "transformer " ++ name ++ "(" ++ intercalate ", " (map prettyStr args) ++ ") -> " ++ prettyStr ret ++ " {"]
        ++ concatMap (map indent . prettyPrint) body
        ++ [ "}" ]

instance PrettyPrint (XType phase) => PrettyPrint (Program phase) where
    prettyPrint (Program decls mainBody) =
        concatMap prettyPrint decls ++ concatMap prettyPrint mainBody

instance PrettyPrint SolExpr where
    prettyPrint (SolBool b) = [ map toLower $ show b ]
    prettyPrint (SolInt i) = [ show i ]
    prettyPrint (SolStr s) = [ show s ]
    prettyPrint (SolAddr addr)  = [ "address(" ++ addr ++ ")" ]
    prettyPrint (SolVar x) = [ x ]
    prettyPrint (FieldAccess e x) = [ prettyStr e ++ "." ++ x ]
    prettyPrint (SolPostInc e) = [ prettyStr e ++ "++" ]
    prettyPrint (SolNot e) = [ "!" ++ "(" ++ prettyStr e ++ ")" ]
    prettyPrint (SolCall recv args) = [ prettyStr recv ++ "(" ++ intercalate ", " (map prettyStr args) ++ ")" ]
    prettyPrint (SolIdx e idxE) = [ prettyStr e ++ "[" ++ prettyStr idxE ++ "]" ]
    prettyPrint (SolAdd e1 e2) = [ "(" ++ prettyStr e1 ++ ") + (" ++ prettyStr e2 ++ ")" ]
    prettyPrint (SolSub e1 e2) = [ "(" ++ prettyStr e1 ++ ") - (" ++ prettyStr e2 ++ ")" ]
    prettyPrint (SolOr e1 e2) = [ "(" ++ prettyStr e1 ++ ") || (" ++ prettyStr e2 ++ ")" ]
    prettyPrint (SolLt e1 e2) = [ "(" ++ prettyStr e1 ++ ") < (" ++ prettyStr e2 ++ ")" ]
    prettyPrint (SolLte e1 e2) = [ "(" ++ prettyStr e1 ++ ") <= (" ++ prettyStr e2 ++ ")" ]
    prettyPrint (SolEq e1 e2) = [ "(" ++ prettyStr e1 ++ ") == (" ++ prettyStr e2 ++ ")" ]

instance PrettyPrint SolStmt where
    prettyPrint (ExprStmt e) = [prettyStr e ++ ";"]
    prettyPrint (SolVarDefInit decl e) = [ prettyStr decl ++ " = " ++ prettyStr e ++ ";" ]
    prettyPrint (SolVarDef decl) = [ prettyStr decl ++ ";" ]
    prettyPrint (SolAssign e1 e2) = [ prettyStr e1 ++ " = " ++ prettyStr e2 ++ ";" ]
    prettyPrint (Delete e) = ["delete " ++ prettyStr e ++ ";"]
    prettyPrint (SolRevert e) = ["revert(" ++ prettyStr e ++ ");"]
    prettyPrint (Require e err) = ["require(" ++ prettyStr e ++ ", " ++ prettyStr err ++ ");"]
    prettyPrint (For init cond step body) =
        ["for (" ++ prettyStr init ++ " " ++ prettyStr cond ++ "; " ++ prettyStr step ++ ") {"]
        ++ concatMap (map indent . prettyPrint) body
        ++ [ "}" ]
    prettyPrint (If cond thenBody) =
        ["if (" ++ prettyStr cond ++ ") {"]
        ++ concatMap (map indent . prettyPrint) thenBody
        ++ [ "}" ]
    prettyPrint (IfElse cond thenBody elseBody) =
        ["if (" ++ prettyStr cond ++ ") {"]
        ++ concatMap (map indent . prettyPrint) thenBody
        ++ [ "} else {" ]
        ++ concatMap (map indent . prettyPrint) elseBody
        ++ [ "}" ]
    prettyPrint (SolTry e rets tryBody catchBody) =
        ["try " ++ prettyStr e ++ " returns (" ++ intercalate ", " (map prettyStr rets) ++ ") {"]
        ++ concatMap (map indent . prettyPrint) tryBody
        ++ [ "} catch {" ]
        ++ concatMap (map indent . prettyPrint) catchBody
        ++ [ "}" ]

instance PrettyPrint DataLoc where
    prettyPrint Memory = ["memory"]
    prettyPrint Calldata = ["calldata"]
    prettyPrint Storage = ["storage"]

instance PrettyPrint Visibility where
    prettyPrint Public = ["public"]
    prettyPrint Private = ["private"]
    prettyPrint Internal = ["internal"]
    prettyPrint External = ["external"]

instance PrettyPrint SolType where
    prettyPrint (SolTypeName s) = [ s ]
    prettyPrint (SolArray t) = [ prettyStr t ++ "[]" ]
    prettyPrint (SolMapping k v) = [ "mapping (" ++ prettyStr k ++ " => " ++ prettyStr v ++ ")" ]

instance PrettyPrint SolVarDecl where
    prettyPrint (SolVarLocDecl t loc x) = [ prettyStr t ++ " " ++ prettyStr loc ++ " " ++ x ]
    prettyPrint (SolVarDecl t x) = [ prettyStr t ++ " " ++ x ]

instance PrettyPrint SolDecl where
    prettyPrint (Struct name varDecls) =
        [ "struct " ++ name ++ " {" ]
        ++ map (indent . (++";") . prettyStr) varDecls
        ++ [ "}" ]
    prettyPrint (Function name args vis rets body) =
        [ "function " ++ name ++ "(" ++ intercalate ", " (map prettyStr args) ++ ") " ++ prettyStr vis ++ " returns (" ++ intercalate ", " (map prettyStr rets) ++ ") {" ]
        ++ concatMap (map indent . prettyPrint) body
        ++ [ "}" ]
    prettyPrint (Constructor args body) =
        [ "constructor (" ++ intercalate ", " (map prettyStr args) ++ ") {" ]
        ++ concatMap (map indent . prettyPrint) body
        ++ [ "}" ]
    prettyPrint (FieldDef v) = [ prettyStr v ++ ";" ]

instance PrettyPrint Contract where
    prettyPrint (Contract ver name decls) =
        -- TODO: Should probably allow customizing this license at some point, but I just put MIT for now (2020-12, I hope you're not reading this years later) to make solc quiet.
        [ "// SPDX-License-Identifier: MIT",
          "pragma solidity ^" ++ ver ++ ";",
          "contract " ++ name ++ " {" ]
        ++ concatMap (map indent . prettyPrint) decls
        ++ [ "}" ]

