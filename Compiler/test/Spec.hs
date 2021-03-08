{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

import Control.Lens ((^.))

import Data.Either (isRight)

import Test.Hspec

import Text.Parsec (parse, many, eof)

import Control.Monad.State

import AST
import Env
import Preprocessor
import Parser
import Phase
import Compiler
import Transform
import Typechecker

main :: IO ()
main = hspec $ do
    preprocessorTests
    parserTests
    compilerTests

parseAndCheck parser str =
    case parse parser "" str of
        res@Left{} -> do
            res `shouldSatisfy` isRight -- We want to fail
            undefined
        Right term -> pure term

x `shouldParseTo` stmtsStr = do
    res <- parseAndCheck (many parseStmt <* eof) stmtsStr
    x `shouldReturn` res

-- | A version of evalState that asserts that there were no errors before returning the result
evalEnv env toEval = do
    let (res, finalEnv) = runState toEval env
    finalEnv^.errors `shouldBe` []
    pure res

evalStr prog = do
    parsed <- parseAndCheck parseProgram prog
    (Program _ progStmts) <- evalEnv (newEnv Preprocessor) (preprocess parsed)
    pure progStmts

shouldPreprocessAs :: State (Env Typechecking) [Stmt Typechecking] -> String -> IO ()
x `shouldPreprocessAs` prog = do
    stmts <- evalEnv (newEnv Preprocessor) x
    progStmts <- parseAndCheck (many parseStmt <* eof) prog
    let transformedStmts = evalState (mapM (transformStmt @Preprocessing @Typechecking @Typechecking) progStmts) $ newEnv Preprocessor
    stmts `shouldBe` transformedStmts

preprocessorTests = do
    describe "preprocessCond" $ do
        it "expands simple preconditions" $ do
            preprocessCond (BinOp OpLe (Var "x") (Var "y"))
                `shouldPreprocessAs` "y --[ x ]-> y"

            preprocessCond (BinOp OpEq (Select (Var "x") (Var "vs")) (Var "y"))
                `shouldPreprocessAs` unlines ["x[vs] --[ y ]-> x[vs]",
                                              "y --[ x[vs] ]-> y"]

            preprocessCond (BinOp OpLe (IntConst 1) (IntConst 3))
                `shouldPreprocessAs` unlines ["1 --> var v0 : nat",
                                              "3 --> var v1 : nat",
                                              "v1 --[ v0 ]-> v1"]

        it "expands conjunctions of preconditions" $ do
            preprocessCond (Conj [BinOp OpNe (Var "x") (Var "y"), BinOp OpIn (IntConst 0) (Var "x")])
                `shouldPreprocessAs` unlines ["try {",
                                         "    x --[ y ]-> x",
                                         "    y --[ x ]-> y",
                                         "    revert",
                                         "} catch {}",
                                         "0 --> var v0 : nat",
                                         "x --[ [ any nat; v0 ] ]-> x"]

        it "expands disjunctions of preconditions" $ do
            preprocessCond (Disj [NegateCond (BinOp OpIn (IntConst 0) (Var "z")), BinOp OpEq (Var "x") (Var "z")])
                `shouldPreprocessAs` unlines ["try {",
                                         "    0 --> var v0 : nat",
                                         "    try {",
                                         "        z --[ [ any nat; v0] ]-> z",
                                         "        revert",
                                         "    } catch {}",
                                         "} catch {",
                                         "    x --[ z ]-> x",
                                         "    z --[ x ]-> z",
                                         "}"]

    describe "expandNegate" $ do
        it "pushes negations down to the atomic conditions" $ do
            cond <- parseAndCheck parsePrecondition "(0 = 1) and (x = y or 0 < 10)"
            expected <- parseAndCheck parsePrecondition "(0 != 1) or (x != y and 0 >= 10)"
            expandNegate cond `shouldBe` expected

    describe "preprocess" $ do
        it "infers ommitted any type quantities" $ do
            complete <- evalStr "[ any nat ; ] --> var m : map any nat => any nat"
            inferred <- evalStr "[ nat ; ] --> var m : map nat => nat"
            inferred `shouldBe` complete

        it "infers ommitted one type quantities" $ do
            complete <- evalStr "[ one address ; ] --> var m : map one address => one address"
            inferred <- evalStr "[ address ; ] --> var m : map address => address"
            inferred `shouldBe` complete

        it "infers user defined fungible types as any" $ do
            let defineType = "type Token is fungible asset nat"
            complete <- evalStr $ unlines [defineType, "[ Token ; ] --> var tokens : list Token"]
            inferred <- evalStr $ unlines [defineType, "[ any Token ; ] --> var tokens : list any Token"]
            inferred `shouldBe` complete

        it "infers missing types on record members" $ do
            complete <- evalStr $ "{ x : any nat |-> 12, y : one bool |-> false } --> var r : { x : any nat, y : one bool }"
            inferred <- evalStr $ "{ x |-> 12, y |-> false } --> var r : { x : nat, y : bool }"
            inferred `shouldBe` complete

        it "infers missing types on (nonempty) multiset literals" $ do
            complete <- evalStr $ "[ any nat; 0,1 ] --> var xs : list any nat"
            inferred <- evalStr $ "[ 0,1 ] --> var xs : list nat"
            inferred `shouldBe` complete

        it "infers missing types using declared variables" $ do
            let header = ["type Token is unique immutable asset nat",
                          "0 --> new Token() --> var tok : Token"]
            complete <- evalStr $ unlines $ header ++
                                            ["var newAccount : { owner : one address, balance : one list one Token } <-- {",
                                             "    owner : one address |-> 0x123,",
                                             "    balance : any list one Token |-> [ one Token ; tok ]",
                                             "}"]
            inferred <- evalStr $ unlines $ header ++
                                            ["var newAccount : { owner : address, balance : list Token } <-- {",
                                             "    owner |-> 0x123,",
                                             "    balance |-> [ tok ]",
                                             "}"]
            inferred `shouldBe` complete

parserTests = do
    describe "parseStmt" $ do
        it "parses simple flows" $ do
            parse parseStmt "" "x --> y"
                `shouldBe` Right (Flow (Var "x") (Var "y"))
            parse parseStmt "" "[ any nat ; ] --> var m : map any nat => any nat"
                `shouldBe` Right (Flow (Multiset (Complete (Any, Nat)) []) (
                    NewVar "m" (Table ["key"] (Complete (One, Record ["key"] [VarDef "key" (Complete (Any, Nat)), VarDef "value" (Complete (Any, Nat))])))))

        it "parses simple backwards flows" $
            parse parseStmt "" "y <-- 1"
                `shouldBe` Right (Flow (IntConst 1) (Var "y"))

        it "parses transformer flows" $
            parse parseStmt "" "x --> f() --> var t : nat"
                `shouldBe` Right (FlowTransform (Var "x") (Call "f" []) (NewVar "t" Nat))

        it "parses backwards transformer flows" $
            parse parseStmt "" "var ts : multiset any nat <-- g(y) <-- [ any nat; ]"
                `shouldBe` Right (FlowTransform (NewVar "ts" (Table [] (Complete (Any, Nat)))) (Call "g" [Var "y"]) (Multiset (Complete (Any, Nat)) []))

        it "parses try-catch statements" $
            parse parseStmt "" "try {} catch {}"
                `shouldBe` Right (Try [] [])

        it "parses flows with selector arrow" $
            parse parseStmt "" "x --[ 5 ]-> y"
                `shouldBe` Right (Flow (Select (Var "x") (IntConst 5)) (Var "y"))

        it "parses backwards flows with selector arrow" $
            parse parseStmt "" "var t : bool <-[ z ]-- [ any bool; true, false] "
                `shouldBe` Right (Flow (Select (Multiset (Complete (Any, PsaBool)) [BoolConst True, BoolConst False]) (Var "z")) (NewVar "t" PsaBool))

        it "parses flows with filters" $ do
            parse parseStmt "" "A --[ nonempty such that isWinner(winNum) ]-> var winners : mutliset one Ticket"
                `shouldBe` Right (Flow (Filter (Var "A") Nonempty "isWinner" [Var "winNum"]) (NewVar "winners" (Named "mutliset")))

        it "parses backwards flows with filters" $ do
            parse parseStmt "" "vals <-[ any such that nonzero() ]-- src"
                `shouldBe` Right (Flow (Filter (Var "src") Any "nonzero" []) (Var "vals"))

        it "parses preconditions" $ do
            parse parseStmt "" "only when 1 < 2"
                `shouldBe` Right (OnlyWhen (BinOp OpLt (IntConst 1) (IntConst 2)))
            parse parseStmt "" "only when x = y and z in w"
                `shouldBe` Right (OnlyWhen (Conj [BinOp OpEq (Var "x") (Var "y"), BinOp OpIn (Var "z") (Var "w")]))
            parse parseStmt "" "only when x > y or !(x in z and u != k)"
                `shouldBe` Right (OnlyWhen (Disj [BinOp OpGt (Var "x") (Var "y"), NegateCond (Conj [BinOp OpIn (Var "x") (Var "z"), BinOp OpNe (Var "u") (Var "k")])]))

        it "parses revert" $ do
            parse parseStmt "" "revert"
                `shouldBe` Right Revert

compilerTests = do
    describe "receiveValue" $ do
        it "subtracts from uint types flowed into consume " $ do
            stmts <- evalEnv (newEnv Compiler) (receiveValue Nat (SolVar "x") (SolVar "x") Consume)
            stmts `shouldBe` [SolAssign (SolVar "x") (SolSub (SolVar "x") (SolVar "x"))]

        it "deletes non-uint types flowed into consume" $ do
            stmts <- evalEnv (newEnv Compiler) (receiveValue PsaBool (SolVar "x") (SolVar "x") Consume)
            stmts `shouldBe` [Delete (SolVar "x")]
