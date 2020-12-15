{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Parser where

import Text.Parsec hiding (Empty)

import AST

type Parser a = forall s st m. Stream s m Char => ParsecT s st m a

parseProgram :: Parser Program
parseProgram = Program <$> many parseDecl <*> many parseStmt

parseDecl :: Parser Decl
parseDecl = try parseTypeDecl <|> try parseTransformerDecl

parseTypeDecl :: Parser Decl
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

parseTransformerDecl :: Parser Decl
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

parseVarDef :: Parser VarDef
parseVarDef = do
    name <- parseVarName
    symbol $ string ":"
    (name,) <$> parseType

parseStmt :: Parser Stmt
parseStmt = try parseFlowTransform <|> try parseFlow

parseFlow :: Parser Stmt
parseFlow = do
    src <- parseLocator
    symbol $ string "-->"
    dst <- parseLocator
    pure $ Flow src dst

parseFlowTransform :: Parser Stmt
parseFlowTransform = do
    src <- parseLocator
    symbol $ string "-->"
    transformer <- parseTransformer
    symbol $ string "-->"
    dst <- parseLocator
    pure $ FlowTransform src transformer dst

parseTransformer :: Parser Transformer
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

parseLocator :: Parser Locator
parseLocator = try parseAddr <|>
               try parseInt <|>
               try parseBool <|>
               try parseString <|>
               try parseNewVar <|>
               try parseVar <|>
               try parseMultiset

parseLocators :: Parser [Locator]
parseLocators = parseDelimList "," parseLocator

parseMultiset :: Parser Locator
parseMultiset = do
    symbol $ string "["
    t <- symbol parseType
    symbol $ string ";"
    elems <- parseLocators
    symbol $ string "]"
    pure $ Multiset t elems

parseVar :: Parser Locator
parseVar = Var <$> parseVarName

parseVarName :: Parser String
parseVarName = do
    c <- symbol $ oneOf prefix
    suf <- many $ oneOf cs
    pure $ c:suf
    where
        prefix = ['a'..'z'] ++ ['A'..'Z'] ++ ['_']
        cs = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['_']

parseNewVar :: Parser Locator
parseNewVar = do
    string "var"
    x <- symbol parseVarName
    symbol $ string ":"
    t <- symbol parseBaseType
    pure $ NewVar x t

parseType :: Parser Type
parseType = (,) <$> symbol parseQuant <*> symbol parseBaseType

parseQuant :: Parser TyQuant
parseQuant = parseConst "empty" Empty <|>
             parseConst "any" Any <|>
             parseConst "one" One <|>
             parseConst "nonempty" Nonempty

parseBaseType :: Parser BaseType
parseBaseType = parseConst "nat" Nat <|>
                parseConst "bool" PsaBool <|>
                parseConst "string" PsaString <|>
                parseConst "address" Address <|>
                parseMultisetType <|>
                parseRecordType <|>
                parseNamedType

parseRecordType :: Parser BaseType
parseRecordType = do
    symbol $ string "{"
    fields <- parseDelimList "," parseVarDef
    symbol $ string "}"

    pure $ Record [] fields

parseNamedType :: Parser BaseType
parseNamedType = Named <$> parseVarName

parseMultisetType :: Parser BaseType
parseMultisetType = do
    symbol $ string "list" -- TODO: Change this
    Table [] <$> parseType

parseInt :: Parser Locator
parseInt = IntConst . read <$> many1 digit

parseBool :: Parser Locator
parseBool = BoolConst <$> (parseConst "true" True <|> parseConst "false" False)

parseAddr :: Parser Locator
parseAddr = do
    string "0x"
    AddrConst <$> many (oneOf "1234567890abcdef")

parseString :: Parser Locator
parseString = StrConst <$> (between (string "\"") (string "\"") $ many $ noneOf "\"")

whitespace :: Parser ()
whitespace = do
    oneOf " \r\t\n"
    pure ()

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
    many $ notFollowedBy $ string "*/"
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

