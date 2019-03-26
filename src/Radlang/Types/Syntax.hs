-- |Types that describe raw AST. Everything marked with \"Raw\" prefix indicates
--toplevel parsing objects that face the programmer.
module Radlang.Types.Syntax where

import           Data.List.NonEmpty

import           Data.Set
import           Radlang.Types.General
import           Radlang.Types.Typesystem (Kind)


-- |Raw representation of type in syntax
data RawType
  = RawTypeWobbly Name
  | RawTypeRigid Name
  | RawTypeApp RawType (NonEmpty RawType)
  | RawTypeFunc RawType RawType
  deriving (Eq, Show, Ord)


-- |All objects that RawProgram may consist of – helps parsing
data RawProgramPart
  = RPNewType RawNewType
  | RPTypeDecl RawTypeDecl
  | RPDataDef RawDataDef
  | RPClassDef RawClassDef
  | RPImplDef RawImplDef
  deriving (Eq, Show)


-- |AST of program
data RawProgram = RawProgram
  { rawprgNewTypes  :: [RawNewType]
  , rawprgTypeDecls :: [RawTypeDecl]
  , rawprgDataDefs  :: [RawDataDef]
  , rawprgClassDefs :: [RawClassDef]
  , rawprgImplDefs  :: [RawImplDef]
  }
  deriving (Eq, Show)


-- |Abstract syntax tree that faithfully represents code. Layer between text and Expr
data RawExpr
  = RawExprVal Name
  | RawExprLit Literal
  | RawExprApplication RawExpr (NonEmpty RawExpr)
  | RawExprLet (NonEmpty (Either RawTypeDecl RawDataDef)) RawExpr
  | RawExprLambda (NonEmpty Pattern) RawExpr
  | RawExprIf (NonEmpty (RawExpr, RawExpr)) RawExpr
  | RawExprCase RawExpr (NonEmpty (Pattern, RawExpr))
  | RawExprFor [ForComphr] RawExpr
  | RawExprList [RawExpr]
  deriving(Eq, Show)


-- |For comprehension to ease monadic programming
data ForComphr
  = ForVal RawExpr
  | ForBind Name RawExpr
  deriving (Eq, Show)


-- |Literal like "lol" or 2138 or 0.42
data Literal
  = LitInt Integer
  | LitString String
  | LitChar Char
  deriving (Eq, Show, Ord)


-- |Possible pattern variations for pattern matching
data Pattern
  = PVar Name
  | PWildcard
  | PAs Name Pattern
  | PLit Literal
  | PConstructor Name [Pattern]
  deriving (Eq, Show, Ord)


-- |AST version of predicate that type belongs to a class
data RawPred = RawPred
 { rpClass :: Name
 , rpType  :: RawType
 } deriving (Eq, Ord, Show)


-- |AST version of qualification of `a` with list of predicates
data RawQual a = RawQual
  { rqPreds   :: [RawPred]
  , rqContent :: a
  } deriving (Eq, Ord, Show)


-- |`newtype` definition
data RawNewType = RawNewType
  { rawntName   :: Name
  , rawntArgs   :: [(Name, Kind)]
  , rawntContrs :: [RawConstructorDef]}
  deriving (Eq, Ord, Show)


-- |Definition of constructor
data RawConstructorDef = RawConstructorDef
  { rawcondefName :: Name
  , rawcondefArgs :: [RawType]}
  deriving (Eq, Ord, Show)


-- |AST version of binding type declaration
data RawTypeDecl = RawTypeDecl
  { rawtdeclName :: Name
  , rawtdeclType :: (RawQual RawType)}
  deriving (Eq, Ord, Show)


-- |AST version of binding value
data RawDataDef = RawDataDef
  { rawdatadefName :: Name
  , rawdatadefArgs :: [Pattern]
  , rawdatadefVal  :: RawExpr}
  deriving (Eq, Show)


-- |AST version of typeclass definition
data RawClassDef = RawClassDef
  { rawclassdefName    :: Name
  , rawclassdefArg     :: Name
  , rawclassdefKind    :: Kind
  , rawclassdefSuper   :: (Set Name)
  , rawclassdefMethods :: [RawTypeDecl]}
  deriving (Eq, Show)


-- |Implementation of interface
data RawImplDef = RawImplDef
  { rawimpldefClass   :: Name
  , rawimpldefType    :: RawQual RawType
  , rawimpldefMethods :: [RawDataDef]}
  deriving (Eq, Show)
