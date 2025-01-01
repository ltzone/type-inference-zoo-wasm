{-# LANGUAGE ImportQualifiedPost #-}

module Parser (parseTrm) where

import Control.Monad (void)
import Control.Monad.Combinators.Expr
import Data.Void (Void)
import Syntax
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L
import Unbound.Generics.LocallyNameless (Bind, bind, s2n)

type Parser = Parsec Void String

parseTrm :: String -> Either String Trm
parseTrm s =
  case runParser (whole trm) "" s of
    Left err -> Left $ errorBundlePretty err
    Right e -> Right e

-- | Top-level parsers (should consume all input)
whole :: Parser a -> Parser a
whole p = sc *> p <* eof

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

trm :: Parser Trm
trm = makeExprParser appTrm trmOps

trmOps :: [[Operator Parser Trm]]
trmOps =
  [ [ InfixL (BinOp OpAdd <$ symbol "+"),
      InfixL (BinOp OpSub <$ symbol "-")
    ],
    [ InfixL (BinOp OpMul <$ symbol "*"),
      InfixL (BinOp OpDiv <$ symbol "/")
    ]
  ]

appTrm :: Parser Trm
appTrm = postfixChain factor app

app :: Parser (Trm -> Trm)
app = do
  e <- factor
  return (`App` e)

factor :: Parser Trm
factor = postfixChain atom annOp

annOp :: Parser (Trm -> Trm)
annOp = do
  symbol ":"
  t <- typ
  return (`Ann` t)

atom :: Parser Trm
atom =
  choice
    [ trmBind Lam $ symbol "\\",
      letRec,
      letExp,
      ifExp,
      try tuple,
      Var . s2n <$> identifier,
      LitBool True <$ rword "True",
      LitBool False <$ rword "False",
      LitInt <$> int,
      parens trm
    ]

trmBind :: (Bind TmVar Trm -> Trm) -> Parser () -> Parser Trm
trmBind c p = do
  p
  x <- identifier
  symbol "->"
  c . bind (s2n x) <$> trm

letExp :: Parser Trm
letExp = do
  rword "let"
  x <- identifier
  symbol "="
  e1 <- trm
  rword "in"
  Let e1 . bind (s2n x) <$> trm

letRec :: Parser Trm
letRec = do
  rword "letrec"
  x <- identifier
  symbol "="
  e1 <- trm
  rword "in"
  LetRec . bind (s2n x) . (,) e1 <$> trm

ifExp :: Parser Trm
ifExp = do
  rword "if"
  e1 <- trm
  rword "then"
  e2 <- trm
  rword "else"
  If e1 e2 <$> trm

tuple :: Parser Trm
tuple = do
  _ <- symbol "("
  first <- trm
  _ <- symbol ","
  rest <- many (symbol "," *> trm)
  _ <- symbol ")"
  return $ Tuple (first : rest)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

typ :: Parser Typ
typ = makeExprParser aTyp typOps

typOps :: [[Operator Parser Typ]]
typOps = [[InfixR (TArr <$ symbol "->")]]

aTyp :: Parser Typ
aTyp =
  choice
    [tconst, parens typ]

tconst :: Parser Typ
tconst =
  choice
    [TInt <$ rword "Int"]

------------------------------------------------------------------------
-- Misc
------------------------------------------------------------------------

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt = L.skipLineComment "--"
    blockCmnt = L.skipBlockComment "{-" "-}"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser ()
symbol = void . L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

int :: Parser Integer
int = lexeme L.decimal

rword :: String -> Parser ()
rword w = string w *> notFollowedBy alphaNumChar *> sc

postfixChain :: Parser a -> Parser (a -> a) -> Parser a
postfixChain p op = do
  x <- p
  rest x
  where
    rest x =
      ( do
          f <- op
          rest $ f x
      )
        <|> return x

rws :: [String]
rws = ["Int", "Bool", "let", "letrec", "in", "fix", "True", "False", "if", "then", "else"]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p = (:) <$> lowerChar <*> many identChar
    check x =
      if x `elem` rws
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

identChar :: Parser Char
identChar = alphaNumChar <|> oneOf "_'"
