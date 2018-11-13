-- |Not real parsing module, but takes significant part in it. Responsible for
-- turning AST into ready to evaluate expression

module Radlang.Parser.Expr(processAST) where

import Data.List.NonEmpty as LNE

import Radlang.Types

processAST :: AST -> Expr
processAST = \case
  ASTVal v -> Val v
  ASTInt i -> ConstInt i
  ASTBool b -> ConstBool b
  ASTApplication fun args ->
    foldl1 Application (processAST <$> cons fun args)
  ASTLet assgs inWhat ->
    let postassg (name, args, type_, val) = case args of
          [] -> (name, type_, processAST val)
          (h:t) -> (name, type_, processAST $
                     ASTLambda (h:|t) val
                   )
    in Let (toList $ postassg <$> assgs) (processAST inWhat)
  ASTLambda (a:|rest) val -> case rest of
    [] -> Lambda a (processAST val)
    h:t -> Lambda a (processAST $ ASTLambda (h:|t) val)
  ASTIf ((c,t):|rest) els -> case rest of
    [] -> If (processAST c) (processAST t) (processAST els)
    hd:tl -> If
      (processAST c)
      (processAST t)
      (processAST $ ASTIf (hd:|tl) els)
