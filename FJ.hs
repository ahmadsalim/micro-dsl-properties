{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module FJ where

import Data.List

newtype Name = Name String
  deriving (Show, Eq)

type ClassName  = Name
type FieldName  = Name
type MethodName = Name

newtype Prog = Prog { classes :: [Class] }
  deriving (Show, Eq)

data Class = Class
            { class_name :: Name
            , superclass :: ClassName
            , fields :: [Field]
            , constructor :: Constructor
            , methods :: [Method]
            }
   deriving (Show, Eq)

data Field = Field
             { field_type' :: ClassName
             , field_name  :: Name
             }
  deriving (Show, Eq)

data Constructor = Constructor
                   { constructor_arguments       :: [Field]
                   , constructor_superarguments  :: [Field]
                   }
  deriving (Show, Eq)

data Method = Method
              { method_returntype :: ClassName
              , method_name       :: Name
              , method_parameters :: [(ClassName, Name)]
              , method_body       :: Expr
              }
  deriving (Show, Eq)

data Expr = Var Name
          | FieldAccess Expr      FieldName
          | MethodCall  Expr      MethodName [Expr]
          | New         ClassName [Expr]
          | Cast        ClassName Expr
  deriving (Show, Eq)

fieldsOf :: Prog -> Name -> [Field]
fieldsOf prog (Name "Object") = []
fieldsOf prog nm              =
  let Just c = find ((== nm) . class_name) (classes prog)
  in fieldsOf prog (superclass c) ++ fields c

methodsOf :: Prog -> Name -> [Method]
methodsOf prog (Name "Object") = []
methodsOf prog nm               =
  let Just c = find ((== nm) . class_name) (classes prog)
  in methodsOf prog (superclass c) ++ methods c

checkScope :: Prog -> Bool
checkScope prog = all (checkClassScope prog) (classes prog)

checkClassScope :: Prog -> Class -> Bool
checkClassScope prog (Class cn sn cflds (Constructor iflds sflds) meths) =
     iflds == sflds ++ cflds
  && fieldsOf prog sn == sflds
  && all (checkMethodScope prog) meths

checkMethodScope :: Prog -> Method -> Bool
checkMethodScope prog (Method rty mnm pars mbody) = checkExpressionScope prog (map snd pars ++ [Name "this"]) mbody

checkExpressionScope :: Prog -> [Name] -> Expr -> Bool
checkExpressionScope prog env (Var nm)            = nm `elem` env
checkExpressionScope prog env (FieldAccess e f)   =
  checkExpressionScope prog env e && any (any ((== f) . field_name) . fieldsOf prog . class_name) (classes prog)
checkExpressionScope prog env (MethodCall e m es) =
   checkExpressionScope prog env e &&
   any (any (\m' -> length (method_parameters m') == length es && ((== m) . method_name $ m')) . methodsOf prog . class_name) (classes prog) &&
   all (checkExpressionScope prog env) es
checkExpressionScope prog env (New c es)          = length (fieldsOf prog c) == length es && all (checkExpression prog env) es
checkExpressionScope prog env (Cast c e)          = checkExpression prog env e

-- Example Programs

animalProg :: Prog
animalProg = Prog [
  Class (Name "Animal") (Name "Object") [Field (Name "Object") (Name "happiness")]
        (Constructor [Field (Name "Object") (Name "happiness")] [])
        [Method (Name "Object") (Name "friend") [(Name "Animal", Name "other")]
                (FieldAccess (Var (Name "other")) (Name "happiness"))]
  ]
