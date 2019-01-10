module Radlang.Types.Syntax where

import Data.List.NonEmpty

import Data.Set
import Radlang.Types.General
import Radlang.Types.Typesystem(Kind)

data RawType
  = RawTypeWobbly Name
  | RawTypeRigid Name
  | RawTypeApp RawType (NonEmpty RawType)
  | RawTypeFunc RawType RawType
  deriving (Eq, Show, Ord)


data RawProgramPart
  = RPNewType NewType
  | RPTypeDecl RawTypeDecl
  | RPDataDef DataDef
  | RPClassDef ClassDef
  | RPImplDef ImplDef
  deriving (Eq, Show)


data RawProgram = RawProgram
  { rawprgNewTypes :: [NewType]
  , rawprgTypeDecls :: [RawTypeDecl]
  , rawprgDataDefs :: [DataDef]
  , rawprgClassDefs :: [ClassDef]
  , rawprgImplDefs :: [ImplDef]
  }
  deriving (Eq, Show)



-- |Abstract syntax tree that faithfully represents code. Layer between text and Expr
data RawExpr
  = RawExprVal Name
  | RawExprLit Literal
  | RawExprApplication RawExpr (NonEmpty RawExpr)
  | RawExprLet (NonEmpty (Name, [Name], Maybe RawType, RawExpr)) RawExpr
  | RawExprLambda (NonEmpty Name) RawExpr
  | RawExprIf (NonEmpty (RawExpr, RawExpr)) RawExpr
  deriving(Eq, Show)


-- |Literal like "" or 2138 or 0.42
data Literal
  = LitInt Integer
  | LitString String
  deriving (Eq, Show, Ord)


-- |Possible pattern variations for pattern matching
data Pattern
  = PVar Name
  | PWildcard
  | PAs Name Pattern
  | PLit Literal
  | PConstructor Name [Pattern]
  deriving (Eq, Show, Ord)


data RawPred = RawPred
 { rpClass :: Name
 , rpType :: RawType
 } deriving (Eq, Ord, Show)


data RawQual a = RawQual
  { rqPreds :: [RawPred]
  , rqContent :: a
  } deriving (Eq, Ord, Show)

data NewType = NewType
  { ntName :: Name
  , ntArgs :: [(Name, Kind)]
  , ntContrs :: [ConstructorDef]}
  deriving (Eq, Ord, Show)

data ConstructorDef = ConstructorDef
  { condefName :: Name
  , condefArgs :: [RawType]}
  deriving (Eq, Ord, Show)

data RawTypeDecl = RawTypeDecl
  { rawtdeclName :: Name
  , rawtdeclType :: (RawQual RawType)}
  deriving (Eq, Ord, Show)

data DataDef = DataDef
  { datadefName :: Name
  , datadefArgs :: [Pattern]
  , datadefVal :: RawExpr}
  deriving (Eq, Show)

data ClassDef = ClassDef
  { classdefName :: Name
  , classdefArg :: Name
  , classdefKind :: Kind
  , classdefSuper :: (Set Name)
  , classdefMethods :: [RawTypeDecl]}
  deriving (Eq, Show)


data ImplDef = ImplDef
  { impldefClass :: Name
  , impldefType :: RawQual RawType
  , impldefMethods :: [DataDef]}
  deriving (Eq, Show)