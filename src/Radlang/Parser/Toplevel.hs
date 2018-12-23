module Radlang.Parser.Toplevel where

import Control.Monad
import Text.Megaparsec
import Text.Megaparsec.Char

import Data.Map.Strict as M
import Data.Set.Monad as S

import Radlang.Types
import Radlang.Parser.General
import Radlang.Parser.Type
import Radlang.Parser.Expr
import Radlang.Parser.AST
import Radlang.Typechecker

test :: IO ()
test = do
  f <- readFile "examples/toplevel.rdl"
  case parse (program <* eof) "XD" f of
    Left a -> putStrLn $ parseErrorPretty a
    Right p -> putStrLn $ either id printTypeEnv $ typecheck $ [toplevelBindings p]

printTypeEnv :: TypeEnv -> String
printTypeEnv (TypeEnv te) =
  let l :: [(String, TypePoly)]
      l = M.toList te
  in
  unlines $ fmap (\(v, t) -> v <> " : " <> show t) l

toplevelBindings :: [Toplevel] -> BindingGroup
toplevelBindings = Prelude.foldl ins (M.empty, [M.empty]) where
  ins :: BindingGroup -> Toplevel -> BindingGroup
  ins (exs, [imps]) tl = case tl of
    TopTypeDecl n qt -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) ->
        (M.insert n (quantify (S.toList $ free qt) qt, []) exs, [imps])
      (Nothing, Just alts) -> let
        e = M.insert n (quantify (S.toList $ free qt) qt, alts) exs
        i = M.delete n imps
        in (e, [i])
      (Just _, _) -> error "Typedecl duplicate"
    TopValDef n args body -> case (M.lookup n exs, M.lookup n imps) of
      (Nothing, Nothing) -> let
        i = M.insert n [(args, processAST body)] imps
        in (exs, [i])
      (Just (t, alts), Nothing) -> let
        e = M.insert n (t, (args, processAST body):alts) exs
        in (e, [imps])
      (Nothing, Just alts) -> let
        i = M.insert n ((args, processAST body):alts) imps
        in (exs, [i])
      _ -> error "Impossible happened: binding both explicit and implicit"
  ins _ _ = error "ins not implemented for this case"

data Toplevel
  = TopTypeDecl Name (Qual Type)
  | TopValDef Name [Pattern] AST
  deriving (Eq, Show)

program :: Parser [Toplevel]
program =
  sepBy (msum $ fmap try [typeDecl, valDef]) (operator ";;")

typeDecl :: Parser Toplevel
typeDecl = do
  n <- lId
  operator ":"
  t <- qual type_
  pure $ TopTypeDecl n t

qual :: Parser a -> Parser (Qual a)
qual aPars = do
  preds <- sepBy (try predicate) (operator ",")
  when (not (Prelude.null preds)) $ operator ":-"
  a <- aPars
  pure $ preds :=> a

predicate :: Parser Pred
predicate = do
  t <- type_
  word "is"
  cl <- uId
  pure $ IsIn cl t

valDef :: Parser Toplevel
valDef = do
  n <- lId
  args <- many pattern
  operator ":="
  body <- ast
  pure $ TopValDef n args body


pattern :: Parser Pattern
pattern = msum $ fmap try
  [ mzero
  , val
  , wildcard
  , as
  , literalPattern
  -- , nplusk
  , constructor
  ]

val :: Parser Pattern
val = PVar <$> lId

wildcard :: Parser Pattern
wildcard = operator "_" >> pure PWildcard

as :: Parser Pattern
as = do
  n <- lId
  operator "="
  p <- pattern
  pure $ PAs n p

literalPattern :: Parser Pattern
literalPattern = msum $ fmap try
  [ PLit . LitInt <$> signed
  , PLit . LitString <$>
      between (symbol "\"") (symbol "\"") (many alphaNumChar)
  ]

constructor :: Parser Pattern
constructor = do
  cname <- constructorName
  args <- many pattern
  pure $ PConstructor cname args

