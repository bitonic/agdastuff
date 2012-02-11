{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
{-# LANGUAGE OverloadedStrings #-}
module Parse where

import Control.Applicative
import Control.Monad

import System.Environment

import Text.Parsec hiding ((<|>), many)
import Text.Parsec.String

import qualified Text.PrettyPrint as P
import Text.PrettyPrint ((<+>), (<>), Doc, text, render)

data Token
    = LPAREN
    | RPAREN
    | LAMBDA
    | DOT
    | ID String
    | COLON
    | ONE
    | ARR
    deriving (Eq)

lexPos :: Parser a -> (a -> b) -> Parser (b, SourcePos)
lexPos p f = (,) <$> fmap f p <*> getPosition

lexToken :: Parser (Token, SourcePos)
lexToken = lexPos (char '(')    (const LPAREN) <|>
           lexPos (char ')')    (const RPAREN) <|>
           lexPos (char '\\')   (const LAMBDA) <|>
           lexPos (char 'λ')    (const LAMBDA) <|>
           lexPos (char '.')    (const DOT)    <|>
           lexPos (char ':')    (const COLON)  <|>
           lexPos (char '1')    (const ONE)    <|>
           lexPos (string "->") (const ARR)    <|>
           lexPos ((\c -> ID . (c:)) <$> letter <*> many (letter <|> digit)) id

lexer :: Parser [(Token, SourcePos)]
lexer = spaces *> go
  where
    go = (:) <$> (lexToken <* spaces) <*> (eof *> return [] <|> go)

type LambdaParser = Parsec [(Token, SourcePos)] ()

data Type
    = One
    | Arr Type Type
    deriving (Eq)

match :: Token -> LambdaParser Token
match t = token (show . fst) snd
          (\(t',_) -> if t == t' then Just t else Nothing)

parens :: LambdaParser a ->  LambdaParser a
parens = between (match LPAREN) (match RPAREN)

pOne :: LambdaParser Type
pOne =  match ONE *> return One

pArr :: LambdaParser Type
pArr = Arr <$> (pOne <|> parens pType) <*> (match ARR *> pType)

pType :: LambdaParser Type
pType = pOne <|> parens pType <|> pArr

pId :: LambdaParser String
pId = token (show . fst) snd (rec . fst)
  where
    rec (ID s) = Just s
    rec _      = Nothing

data Term
    = Var String
    | App Term Term
    | Lam String Type Term
    deriving (Eq)

pVar :: LambdaParser Term
pVar = fmap Var pId

pLam :: LambdaParser Term
pLam = Lam <$> (match LAMBDA *> pId)
           <*> (match COLON  *> pType)
           <*> (match DOT    *> pTerm)

pTerm :: LambdaParser Term
pTerm = foldl1 App <$> many1 (pVar <|> try (parens pLam) <|> parens pTerm)

lexTerm :: String -> Either ParseError [(Token, SourcePos)]
lexTerm = parse lexer ""

parseTerm :: String -> Either ParseError Term
parseTerm = lexTerm >=> parse pTerm ""

parseFile :: FilePath -> IO Term
parseFile = readFile >=> either (fail . show) return . parseTerm

-- Show

prettyType :: Type -> Doc
prettyType One           = "1"
prettyType (Arr One ty)  = "1" <+> "->" <+> prettyType ty
prettyType (Arr ty1 ty2) = P.parens (prettyType ty1) <+> "->" <+> prettyType ty2

prettyLApp :: Term -> Doc
prettyLApp t@(Var _) = prettyTerm t
prettyLApp t         = P.parens (prettyTerm t)

prettyTerm :: Term -> Doc
prettyTerm (Var v)                 = text v
prettyTerm (App t1@(Lam _ _ _) t2) = P.parens (prettyTerm t1) <+> prettyLApp t2
prettyTerm (App t1             t2) = prettyTerm t1 <+> prettyLApp t2
prettyTerm (Lam v ty t)            =
    "\\" <> text v <+> ":" <+> prettyType ty <+> "." <+> prettyTerm t

instance Show Token where
    show LPAREN = "("
    show RPAREN = ")"
    show LAMBDA = "\\"
    show DOT    = "."
    show (ID s) = s
    show COLON  = ":"
    show ONE    = "1"
    show ARR    = "->"

instance Show Type where
    show = render . prettyType

instance Show Term where
    show = render . prettyTerm

-- Helpers

parseUserFile :: IO Term
parseUserFile = getArgs >>= parseFile . head