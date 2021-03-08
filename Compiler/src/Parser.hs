{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Text.Parsec hiding (Empty)
import Text.Parsec.Expr

import AST
import Phase

type Parser a = forall s st m. Stream s m Char => ParsecT s st m a

parseProgram :: Parser (Program Preprocessing)
parseProgram = do
    prog <- Program <$> many parseDecl <*> many parseStmt
    eof
    pure prog

parseDecl :: Parser (Decl Preprocessing)
parseDecl = try parseTypeDecl <|>
            try parseTransformerDeclNoRet <|>
            try parseTransformerDecl

parseTypeDecl :: Parser (Decl Preprocessing)
parseTypeDecl = do
    symbol $ string "type"
    name <- parseVarName
    symbol $ string "is"
    ms <- many $ symbol parseModifier
    TypeDecl name ms <$> parseBaseType

parseModifier :: Parser Modifier
parseModifier = try (parseConst "fungible" Fungible) <|>
                try (parseConst "asset" Asset) <|>
                try (parseConst "consumable" Consumable) <|>
                try (parseConst "immutable" Immutable) <|>
                try (parseConst "unique" Unique)

parseTransformerDecl :: Parser (Decl Preprocessing)
parseTransformerDecl = do
    symbol $ string "transformer"
    name <- parseVarName
    symbol $ string "("
    args <- parseDelimList "," parseVarDef
    symbol $ string ")"
    symbol $ string "->"
    ret <- parseVarDef
    symbol $ string "{"
    body <- many parseStmt
    symbol $ string "}"
    pure $ TransformerDecl name args ret body

parseTransformerDeclNoRet :: Parser (Decl Preprocessing)
parseTransformerDeclNoRet = do
    symbol $ string "transformer"
    name <- parseVarName
    symbol $ string "("
    args <- parseDelimList "," parseVarDef
    symbol $ string ")"
    symbol $ string "{"
    body <- many parseStmt
    symbol $ string "}"
    pure $ TransformerDecl name args (VarDef "__success" (Complete (Any, PsaBool))) $ body ++ [ Flow (BoolConst True) (Var "__success") ]

parseVarDef :: Parser (VarDef Preprocessing)
parseVarDef = do
    name <- parseVarName
    symbol $ string ":"
    VarDef name <$> parseType

parseStmt :: Parser (Stmt Preprocessing)
parseStmt = try parseFlowTransform <|> try parseFlowTransformBackwards <|>
            try parseFlowSel <|> try parseFlowSelBackwards <|>
            try parseFlowFilter <|> try parseFlowFilterBackwards <|>
            try parseFlow <|> try parseFlowBackwards <|>
            try parseTry <|>
            try parseOnlyWhen <|>
            try (parseConst "revert" Revert)

parseOnlyWhen :: Parser (Stmt Preprocessing)
parseOnlyWhen = do
    symbol $ string "only"
    symbol $ string "when"
    OnlyWhen <$> parsePrecondition

parsePrecondition :: Parser (Precondition Preprocessing)
parsePrecondition = buildExpressionParser precondTable $ symbol parseCondAtom

precondTable :: Stream s m Char => OperatorTable s st m (Precondition Preprocessing)
precondTable =
    [
        [ prefix "!" NegateCond ],
        [ binary "and" (\a b -> Conj [a,b]) AssocLeft,
          binary "or" (\a b -> Disj [a,b]) AssocLeft ]
    ]

binary name f = Infix $ do
    symbol $ string name
    pure f
prefix name f = Prefix $ do
    symbol $ string name
    pure f

parseCondAtom :: Parser (Precondition Preprocessing)
parseCondAtom = try binOpCond <|> try parseBracketedCond

parseBracketedCond :: Parser (Precondition Preprocessing)
parseBracketedCond = between (symbol (string "(")) (symbol (string ")")) parsePrecondition

binOpCond :: Parser (Precondition Preprocessing)
binOpCond = do
    a <- parseLocator
    op <- symbol $ choice $ map try [ parseConst "<=" OpLe, parseConst "<" OpLt,
                                      parseConst ">=" OpGe, parseConst ">" OpGt,
                                      parseConst "=" OpEq, parseConst "!=" OpNe,
                                      parseConst "in" OpIn, parseNotIn ]
    b <- parseLocator
    pure $ BinOp op a b
    where
        parseNotIn = symbol (string "not") >> symbol (string "in") >> pure OpNotIn

parseFlow :: Parser (Stmt Preprocessing)
parseFlow = do
    src <- parseLocator
    symbol $ string "-->"
    dst <- parseLocator
    pure $ Flow src dst

parseFlowBackwards :: Parser (Stmt Preprocessing)
parseFlowBackwards = do
    dst <- parseLocator
    symbol $ string "<--"
    src <- parseLocator
    pure $ Flow src dst

parseFlowSel :: Parser (Stmt Preprocessing)
parseFlowSel = do
    src <- parseLocator
    symbol $ string "--["
    sel <- parseLocator
    symbol $ string "]->"
    dst <- parseLocator
    pure $ Flow (Select src sel) dst

parseFlowSelBackwards :: Parser (Stmt Preprocessing)
parseFlowSelBackwards = do
    dst <- parseLocator
    symbol $ string "<-["
    sel <- parseLocator
    symbol $ string "]--"
    src <- parseLocator
    pure $ Flow (Select src sel) dst

parseFlowFilter :: Parser (Stmt Preprocessing)
parseFlowFilter = do
    src <- parseLocator
    symbol $ string "--["
    q <- parseQuant
    symbol $ string "such"
    symbol $ string "that"
    f <- parseVarName
    symbol $ string "("
    args <- parseLocators
    symbol $ string ")"
    symbol $ string "]->"
    dst <- parseLocator
    pure $ Flow (Filter src q f args) dst

parseFlowFilterBackwards :: Parser (Stmt Preprocessing)
parseFlowFilterBackwards = do
    dst <- parseLocator
    symbol $ string "<-["
    q <- parseQuant
    symbol $ string "such"
    symbol $ string "that"
    f <- parseVarName
    symbol $ string "("
    args <- parseLocators
    symbol $ string ")"
    symbol $ string "]--"
    src <- parseLocator
    pure $ Flow (Filter src q f args) dst

parseFlowTransform :: Parser (Stmt Preprocessing)
parseFlowTransform = do
    src <- parseLocator
    symbol $ string "-->"
    transformer <- parseTransformer
    symbol $ string "-->"
    dst <- parseLocator
    pure $ FlowTransform src transformer dst

parseFlowTransformBackwards :: Parser (Stmt Preprocessing)
parseFlowTransformBackwards = do
    src <- parseLocator
    symbol $ string "<--"
    transformer <- parseTransformer
    symbol $ string "<--"
    dst <- parseLocator
    pure $ FlowTransform src transformer dst

parseTry :: Parser (Stmt Preprocessing)
parseTry = do
    symbol $ string "try"
    symbol $ string "{"
    tryBlock <- many parseStmt
    symbol $ string "}"
    symbol $ string "catch"
    symbol $ string "{"
    catchBlock <- many parseStmt
    symbol $ string "}"
    pure $ Try tryBlock catchBlock

parseTransformer :: Parser (Transformer Preprocessing)
parseTransformer = try parseConstruct <|> try parseCall
    where
        parseConstruct = do
            symbol $ string "new"
            name <- parseVarName
            symbol $ string "("
            args <- parseLocators
            symbol $ string ")"
            pure $ Construct name args

        parseCall = do
            name <- parseVarName
            symbol $ string "("
            args <- parseLocators
            symbol $ string ")"
            pure $ Call name args

parseLocator :: Parser (Locator Preprocessing)
parseLocator = buildExpressionParser locOpTable $ symbol parseLocatorSingle

locOpTable :: Stream s m Char => OperatorTable s st m (Locator Preprocessing)
locOpTable =
    [
        [Postfix $ try $ do
            symbol $ string "."
            x <- parseVarName
            pure $ \l -> Field l x
        ]
        ,
        [ Postfix $ try $ do
            symbol $ string "["
            k <- parseLocatorSingle
            symbol $ string "]"
            pure $ \l -> Select l k
        ]
    ]

parseLocatorSingle :: Parser (Locator Preprocessing)
parseLocatorSingle = try parseAddr <|>
                     try parseInt <|>
                     try parseString <|>
                     try parseBool <|>
                     try parseNewVar <|>
                     try parseMultiset <|>
                     try parseRecordLit <|>
                     try parseConsume <|>
                     try parseVar

parseConsume :: Parser (Locator Preprocessing)
parseConsume = do
    symbol $ string "consume"
    pure Consume

parseRecordLit :: Parser (Locator Preprocessing)
parseRecordLit = do
    symbol $ string "{"
    members <- parseDelimList "," parseRecordMember
    symbol $ string "}"

    pure $ RecordLit [] members

parseRecordMember :: Parser (VarDef Preprocessing, Locator Preprocessing)
parseRecordMember = do
    vdef <- try parseVarDef <|>
            (VarDef <$> parseVarName <*> pure InferredType)
    symbol $ string "|->"
    (vdef,) <$> parseLocator

parseLocators :: Parser [Locator Preprocessing]
parseLocators = parseDelimList "," parseLocator

parseMultiset :: Parser (Locator Preprocessing)
parseMultiset = do
    symbol $ string "["
    t <- option InferredType $ try $ symbol parseType <* symbol (string ";")
    elems <- parseLocators
    symbol $ string "]"
    pure $ Multiset t elems

parseVar :: Parser (Locator Preprocessing)
parseVar = Var <$> parseVarName

parseVarName :: Parser String
parseVarName = do
    c <- oneOf prefix
    suf <- many $ oneOf cs
    pure $ c:suf
    where
        prefix = ['a'..'z'] ++ ['A'..'Z'] ++ ['_']
        cs = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['_']

parseNewVar :: Parser (Locator Preprocessing)
parseNewVar = do
    string "var"
    x <- symbol parseVarName
    symbol $ string ":"
    t <- symbol parseBaseType
    pure $ NewVar x t

parseType :: Parser (InferrableType Preprocessing)
parseType = try parseCompleteType <|>
            try parseInferredType
    where
        parseCompleteType = curry Complete <$> symbol parseQuant <*> symbol parseBaseType
        parseInferredType = Infer <$> symbol parseBaseType


parseQuant :: Parser TyQuant
parseQuant = try (parseConst "empty" Empty) <|>
             try (parseConst "any" Any) <|>
             try (parseConst "one" One) <|>
             try (parseConst "nonempty" Nonempty)

parseBaseType :: Parser (BaseType Preprocessing)
parseBaseType = try (parseConst "nat" Nat) <|>
                try (parseConst "bool" PsaBool) <|>
                try (parseConst "string" PsaString) <|>
                try (parseConst "address" Address) <|>
                try parseMultisetType <|>
                try parseRecordType <|>
                try parseMapType <|>
                try parseNamedType

parseMapType :: Parser (BaseType Preprocessing)
parseMapType = do
    symbol $ string "map"
    keyTy <- parseType
    symbol $ string "=>"
    valTy <- parseType
    pure $ Table ["key"] (Complete (One, Record ["key"] [ VarDef "key" keyTy, VarDef "value" valTy ]))

parseRecordType :: Parser (BaseType Preprocessing)
parseRecordType = do
    symbol $ string "{"
    fields <- parseDelimList "," parseVarDef
    symbol $ string "}"

    pure $ Record [] fields

parseNamedType :: Parser (BaseType Preprocessing)
parseNamedType = Named <$> parseVarName

parseMultisetType :: Parser (BaseType Preprocessing)
parseMultisetType = do
    symbol $ choice [string "list", string "multiset"] -- TODO: Change this
    Table []  <$> parseType

parseInt :: Parser (Locator Preprocessing)
parseInt = IntConst . read <$> symbol (many1 digit)

parseBool :: Parser (Locator Preprocessing)
parseBool = BoolConst <$> symbol (parseConst "true" True <|> parseConst "false" False)

parseAddr :: Parser (Locator Preprocessing)
parseAddr = do
    symbol $ string "0x"
    AddrConst . ("0x"++) <$> many (oneOf "1234567890abcdef")

parseString :: Parser (Locator Preprocessing)
parseString = StrConst <$> symbol (between (string "\"") (string "\"") $ many $ noneOf "\"")

whitespace :: Parser ()
whitespace = oneOf " \r\t\n" >> pure ()

lineSep :: Parser ()
lineSep = skipMany (whitespace <|> try lineComment <|> try blockComment)

lineComment :: Parser ()
lineComment = do
    string "//"
    many $ noneOf "\n"
    pure ()

blockComment :: Parser ()
blockComment = do
    string "/*"
    manyTill anyChar $ try $ string "*/"
    pure ()

symbol :: Stream s m Char => ParsecT s st m a -> ParsecT s st m a
symbol parser = do
    lineSep
    v <- parser
    lineSep
    pure v

parseConst :: Stream s m Char => String -> a -> ParsecT s st m a
parseConst s x = string s >> pure x

parseDelimList :: Stream s m Char => String -> ParsecT s st m a -> ParsecT s st m [a]
parseDelimList sep single = try nonempty <|> nonemptyEnd <|> pure []
    where
        nonemptyEnd = do
            l <- single
            pure [l]
        nonempty = do
            l <- single
            symbol $ string sep
            ls <- parseDelimList sep single
            pure $ l:ls

