{-# LANGUAGE OverloadedStrings, TupleSections #-}

module Parsing
    ( runInitParser, infixOp, variable, integerLiteral, moduleParser, expr
    ) where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void
import VampExp
import Constraints
import qualified Control.Monad.State as St
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Either
import Control.Monad.Combinators.Expr
import Data.Functor

data ParserState = ParserState
    { currentID   :: VariableId
    , varNameToID :: Map String VariableId
    }

initialState :: ParserState
initialState = ParserState 0 Map.empty

type Parser = ParsecT Void String (St.State ParserState)

runInitParser :: Parser a -> String -> (Either (ParseErrorBundle String Void) a, ParserState)
runInitParser p input = St.runState (runParserT p "" input) initialState

spaceComments :: Parser ()
spaceComments = L.space space1 (L.skipLineComment "//" <|> L.skipBlockComment "/*" "*/") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceComments

symbol :: String -> Parser String
symbol = L.symbol spaceComments

keyword :: String -> Parser String
keyword k = string k <* notFollowedBy alphaNumChar <* spaceComments

ident :: Parser String
ident = lexeme $ (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '_')

variablePart :: String -> Parser Variable
variablePart name = do
    state <- St.get
    let mapping = varNameToID state
        current = currentID state
    case Map.lookup name mapping of
        Just i -> return $ Variable (Just name) i
        Nothing -> do
            let newID = current + 1
                newMapping = Map.insert name current mapping
            St.put $ ParserState newID newMapping
            return $ Variable (Just name) current

variable :: Parser Variable
variable = do
    name <- ident
    _ <- spaceComments
    variablePart name

intrinsics :: [String]
intrinsics = ["iter", "fold"]

varOrIntrinsic :: Parser Expr
varOrIntrinsic = do
    name <- ident
    _ <- spaceComments
    if name `elem` intrinsics
    then return $ Intrinsic name
    else variablePart name <&> VarExpr

integerLiteral :: Parser Integer
integerLiteral = do
    n <- choice
        [ try (char '0' >> char 'x' >> L.hexadecimal)
        , try (char '0' >> char 'o' >> L.octal)
        , try (char '0' >> char 'b' >> L.binary)
        , L.decimal
        ]
    _ <- spaceComments
    return n

infixOp :: Parser InfixOp
infixOp = choice 
    [ Divide       <$ symbol "/"
    , Multiply     <$ symbol "*"
    , Add          <$ symbol "+"
    , Subtract     <$ symbol "-"
    , Equal        <$ symbol "="
    , Exponentiate <$ symbol "^"
    , IntDivide    <$ symbol "\\"
    , Modulo       <$ symbol "%"
    , DivideZ      <$ symbol "|"
    ]

pat :: Parser Pat
pat = makeExprParser simplePat operatorTable
    where
    simplePat :: Parser Pat
    simplePat = choice 
        [ Unit       <$ symbol "()"
        , Nil        <$ symbol "[]"
        , ConstP     <$> integerLiteral
        , VarPat     <$> variable
        , between (symbol "(") (symbol ")") pat
        ]

    operatorTable = 
        [ [ InfixR (Pair <$ symbol ",") ]
        , [ InfixR (Cons <$ symbol ":") ]
        ]

letBinding :: Parser LetBinding
letBinding = do
    _ <- keyword "def"
    p <- pat
    _ <- symbol "="
    LetBinding p <$> expr

definition :: Parser Definition
definition = Definition <$> letBinding

moduleParser :: Parser Module
moduleParser = do
    pubVars <- many (keyword "pub" *> variable <* symbol ";")
    items   <- many (definitionOrExpr <* symbol ";")
    let (defs, exprs) = partitionEithers items
    return $ Module pubVars defs exprs
  where
  definitionOrExpr :: Parser (Either Definition Expr)
  definitionOrExpr = (Left <$> definition) <|> (Right <$> expr)

expr :: Parser Expr
expr = makeExprParser (try appE <|> simpleExpr) operatorTable
    where
    simpleExpr :: Parser Expr
    simpleExpr = choice 
        [ UnitE       <$ symbol "()"
        , NilE        <$ symbol "[]"
        , ConstantE   <$> integerLiteral
        , varOrIntrinsic
        , try functionE
        , try letBindingE
        , between (symbol "(") (symbol ")") expr
        ]

    operatorTable = 
        [ [ Prefix (Negate <$ symbol "-") ]
        , [ InfixR (Infix Exponentiate <$ symbol "^") ]
        , [ InfixL (Infix Multiply     <$ symbol "*")
          , InfixL (Infix Divide       <$ symbol "/")
          , InfixL (Infix IntDivide    <$ symbol "\\")
          , InfixL (Infix Modulo       <$ symbol "%")
          , InfixL (Infix And          <$ symbol "|")
        ]
        , [ InfixL (Infix Add         <$ symbol "+")
          , InfixL (Infix Subtract    <$ symbol "-")
        ]
        , [ InfixR (PairE         <$ symbol ",") ]
        , [ InfixR (ConsE         <$ symbol ":") ]
        , [ InfixL (Infix Equal   <$ symbol "=") ]
        , [ InfixL (Infix And     <$ symbol "&") ]
        ]

    functionE :: Parser Expr
    functionE = do
        _ <- keyword "fun"
        pats <- some pat
        _ <- symbol "{"
        e <- expr
        _ <- symbol "}"
        return $ FunctionE pats e

    letBindingE :: Parser Expr
    letBindingE = do
        lb <- letBinding
        _ <- symbol ";"
        LetBindingE lb <$> expr

    appE :: Parser Expr
    appE = do
        es <- simpleExpr `sepBy1` spaceComments
        return $ foldr1 Application es