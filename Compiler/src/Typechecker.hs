{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Typechecker where

import Control.Lens
import Control.Monad.State

import AST
import Env
import Phase
import Transform

instance ProgramTransform Preprocessed Typechecked where
    transformXType = transformQuantifiedType

typecheck :: Program Preprocessed -> State (Env Typechecked) (Program Typechecked)
typecheck prog@(Program decls stmts) = do
    checkedDecls <- mapM checkDecl decls
    checkedStmts <- mapM checkStmt stmts
    pure $ Program checkedDecls checkedStmts

checkDecl :: Decl Preprocessed -> State (Env Typechecked) (Decl Typechecked)
checkDecl = transformDecl

checkStmt :: Stmt Preprocessed -> State (Env Typechecked) (Stmt Typechecked)
checkStmt = transformStmt
