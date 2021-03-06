{-# LANGUAGE ScopedTypeVariables, MultiParamTypeClasses, FlexibleContexts, MultiWayIf, TypeOperators, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module FJ where

import Data.Data
import Data.Typeable
import Data.List
import Data.Maybe
import Data.Either
import Data.Tuple
import Data.Foldable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Graph as Graph

import Data.Generics.Uniplate.Data

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans.Class as Trans
import Control.Monad.Trans.Maybe
import Control.Arrow (second)

import Text.PrettyPrint

import Test.QuickCheck
import qualified Test.LazySmallCheck as LSC

type f $ a = f a

newtype Name = Name { unName :: String }
  deriving (Show, Eq, Ord, Data, Typeable)

type ClassName  = Name
type FieldName  = Name
type MethodName = Name

newtype Prog = Prog { classes :: [Class] }
  deriving (Eq, Data, Typeable)

instance Show Prog where
  show = render . prettyProg

data CachedProg = CachedProg
  { cchProg :: Prog
  , cchSupertypes :: Map ClassName [ClassName]
  , cchFields :: Map ClassName [Field]
  , cchMethods :: Map ClassName [Method]
  }
  deriving (Eq, Show)

data Class = Class
            { className :: Name
            , superclass :: ClassName
            , fields :: [Field]
            , constructor :: Constructor
            , methods :: [Method]
            }
   deriving (Show, Eq, Data, Typeable)

data Field = Field
             { fieldType :: ClassName
             , fieldName  :: Name
             }
  deriving (Show, Eq, Data, Typeable)

data Constructor = Constructor
                   { constructorArguments       :: [Field]
                   , constructorSuperArguments  :: [Field]
                   }
  deriving (Show, Eq, Data, Typeable)

data Method = Method
              { methodReturnType :: ClassName
              , methodName       :: Name
              , methodParameters :: [(ClassName, Name)]
              , methodBodyExpr   :: Expr
              }
  deriving (Show, Eq, Data, Typeable)

data Expr = Var         { exprType :: Maybe ClassName, varName :: Name }
          | FieldAccess { exprType :: Maybe ClassName, fieldAccessTarget :: Expr, fieldAccessName :: FieldName }
          | MethodCall  { exprType :: Maybe ClassName, methodCallTarget :: Expr, methodCallName :: MethodName, methodCallArgs :: [Expr] }
          | New         { exprType :: Maybe ClassName, newInstanceClassName :: ClassName, newInstanceArgs :: [Expr] }
          | Cast        { exprType :: Maybe ClassName, castClassName :: ClassName, castTarget :: Expr }
  deriving (Show, Eq, Data, Typeable)

-- Serial

instance LSC.Serial Prog where
  series = LSC.cons1 Prog

instance LSC.Serial Class where
  series = LSC.cons5 Class

instance LSC.Serial Field where
  series = LSC.cons2 Field

instance LSC.Serial Constructor where
  series = LSC.cons2 Constructor

instance LSC.Serial Method where
  series = LSC.cons4 Method

instance LSC.Serial Expr where
  series =  LSC.cons1 (Var Nothing)
            LSC.\/ LSC.cons2 (FieldAccess Nothing)
            LSC.\/ LSC.cons3 (MethodCall Nothing)
            LSC.\/ LSC.cons2 (New Nothing)
            LSC.\/ LSC.cons2 (Cast Nothing)

instance LSC.Serial Name where
  series = LSC.cons1 Name

-- Generators
unique :: Eq a => [a] -> Bool
unique xs = nub xs == xs

newtype Readable = Readable { getReadable :: String }

instance Arbitrary Readable where
  arbitrary = do
    len <- (getSmall . getPositive) <$> arbitrary
    Readable <$> vectorOf len (elements (['A' .. 'Z'] ++ ['a'..'z']))

updateCachedProg :: CachedProg -> Class -> Maybe CachedProg
updateCachedProg cprog class' =
  let prog = cchProg cprog
      super = superclass class'
      supertypes = cchSupertypes cprog
      allFields = cchFields cprog
      allMethods = cchMethods cprog
  in if |  Just supersuperty <- Map.lookup (superclass class') supertypes
         , Just superFields  <- Map.lookup (superclass class') allFields
         , Just superMethods <- Map.lookup (superclass class') allMethods ->
              return cprog {
                  cchProg = prog { classes = class' : classes prog }
                , cchSupertypes = Map.insert (className class') (
                    superclass class' : supersuperty) supertypes
                , cchFields = Map.insert (className class') (
                  fields class' ++ superFields) allFields
                , cchMethods = Map.insert (className class') (
                  methods class' ++ superMethods) allMethods
              }
        | otherwise -> Nothing

emptyCachedProg :: CachedProg
emptyCachedProg =  CachedProg (Prog []) (Map.singleton (Name "Object") [])
                                        (Map.singleton (Name "Object") [])
                                        (Map.singleton (Name "Object") [])

makeCached :: Prog -> Maybe CachedProg
makeCached prog =
  let classKeyMap = Map.fromList $
        zipWith (\(cn, c) k -> (cn, (c, k))) (map (\c -> (className c, c)) $ classes prog) [1..]
      (g,vm) = Graph.graphFromEdges' $ map (\(cn, (c, k)) ->
                                              (c, k, toList (snd <$> Map.lookup (superclass c) classKeyMap)))
                                           (Map.toList classKeyMap)
  in foldlM updateCachedProg emptyCachedProg . map ((\(c,_,_) -> c) . vm) $ reverse $ Graph.topSort g

genProgramScoped :: Int -> Gen Prog
genProgramScoped size = do
  cnames <- nub <$> resize (size `div` 2) (listOf1 genName)
  _objc : cs <- reverse <$> foldrM (\cn gp1 -> (: gp1) <$>
                                ((\(c,fs,ms,sp) -> (c,fs,ms,Just sp)) <$> genClassP1Scoped gp1 cn (size `div` length cnames)))
                                 [(Name "Object", [], [], Nothing)] cnames
  let cs' = map (\(c,fs,ms,Just sp) -> (c,fs,ms,sp)) cs
  cchProg <$> foldlM (\prevProg ci ->
                        (fromJust . updateCachedProg prevProg) <$>
                          genClassScoped prevProg cs' ci (size `div` length cs'))
         emptyCachedProg [0 .. length cs' - 1]

genClassP1Scoped :: [(ClassName, [FieldName], [(MethodName, Int)], Maybe ClassName)] -> ClassName -> Int -> Gen (ClassName, [FieldName], [(MethodName, Int)], ClassName)
genClassP1Scoped prevClasses cn size = do
  (super, superfs, superms, _) <- elements prevClasses
  (,,,) <$> pure cn
        <*> ((superfs ++) <$> (nub <$> resize (size `div` 2) (listOf genName)))
        <*> ((superms ++) <$> (nub <$> resize (size `div` 2) (listOf ((,) <$> genName <*> ((getSmall . getPositive) <$> arbitrary)))))
        <*> pure super

genClassScoped :: CachedProg -> [(ClassName, [FieldName], [(MethodName, Int)], ClassName)] -> Int -> Int -> Gen Class
genClassScoped prevProg classes index size = do
  let (cn, fs, ms, sn) = classes !! index
  let Just sfvals = fieldsOf prevProg sn
  let allcs = map (\(c,fs,_,_) -> (c, length fs)) classes
  let allfs = concatMap (\(_,fs,_,_) -> fs) classes
  let allms = concatMap (\(_,_,ms,_) -> ms) classes
  let specificfs = fs \\ map fieldName sfvals
  fieldvals <- mapM (genFieldScoped (map (\(c,_,_,_) -> c) classes)) specificfs
  Class cn sn fieldvals (Constructor (sfvals ++ fieldvals) sfvals) <$>
    mapM (\m -> genMethodScoped allcs allfs allms m ((size - length fs) `div` length ms)) ms

genFieldScoped :: [ClassName] -> FieldName -> Gen Field
genFieldScoped classes fn = Field <$> elements classes <*> pure fn

genMethodScoped :: [(ClassName, Int)] -> [FieldName] -> [(MethodName, Int)] -> (MethodName, Int) -> Int -> Gen Method
genMethodScoped classes fields methods (methodnm, argcount) size = do
    params <- zip <$> vectorOf argcount (fst <$> elements classes)
                  <*> (vectorOf argcount genName `suchThat` unique)
    Method <$> (fst <$> elements classes) <*> pure methodnm <*> pure params
           <*> genExprScoped classes fields methods (map snd params ++ [Name "this"]) size

genExprScoped :: [(ClassName, Int)] -> [FieldName] -> [(MethodName, Int)] -> [Name] -> Int -> Gen Expr
genExprScoped classes fields methods env = go
  where go size = oneof $ [ Var Nothing <$> elements env | not (null env) ] ++
                           [ FieldAccess Nothing <$> go (size - 1) <*> elements fields | not (null fields) && size > 0 ] ++
                           [ do (m, argcount) <- elements methods
                                MethodCall Nothing <$> go (size `div` (argcount + 1) ) <*> pure m <*> vectorOf argcount (go (size - 1)) | not (null methods) && size > 0 ] ++
                           [ do (c, argcount) <- elements classes
                                New Nothing <$> pure c <*> vectorOf argcount (go (size `div` (argcount + 1))) | not (null classes) && size > 0 ] ++
                           [ Cast Nothing <$> (fst <$> elements classes) <*> go (size - 1) | not (null classes) && size > 0 ]

genName :: Gen Name
genName = (Name . getReadable) <$> arbitrary

genProgramTyped :: Int -> Gen (Maybe Prog)
genProgramTyped size = do
  classCount <- choose (1, floor . sqrt . fromIntegral $ size)
  _objc:classesP1 <- reverse <$> foldrM (\_ prevClasses -> (:) <$> fmap (second Just) (genClassP1Typed (reverse prevClasses))
                                                               <*> pure prevClasses)
                     [(Name "Object", Nothing)] [0..classCount - 1]
  let size' = (max 0 $ size - classCount) `div` classCount
  let classesP1' = map (\(cn, Just scn) -> (cn,scn)) classesP1
  _objc:classesP2 <- (reverse . fst) <$> foldlM (\(prevClasses, _:nextClasses) cp1 ->
                         (,) <$> ((:) <$> ((\(cn,fs,ms,scn) -> (cn,fs,ms,Just scn)) <$>
                                  genClassP2Typed (reverse prevClasses) nextClasses cp1 size') <*> pure prevClasses)
                             <*> pure nextClasses) ([(Name "Object", [], [], Nothing)], classesP1') classesP1'
  let classesP2' = fmap (\(cn,fs,ms, Just scn) -> (cn,fs,ms,scn)) classesP2
  (cchProg <$>) <$> runMaybeT (foldlM (\prevProg ci ->
                          (fromJust . updateCachedProg prevProg) <$>
                            MaybeT (genClassTyped prevProg classesP2' ci (size' `div` 2)))
                              emptyCachedProg [0 .. length classesP2' - 1])


genClassP1Typed :: [(ClassName, Maybe ClassName)] -> Gen (ClassName, ClassName)
genClassP1Typed prevClasses = do
  super <- frequency $ fmap (\(c,_) -> (if unName c == "Object" then 1 else 5, return c)) prevClasses
  (,) <$> genName <*> pure super

genClassP2Typed :: [(ClassName, [Field], [(MethodName, [ClassName], ClassName)], Maybe ClassName)] -> [(ClassName, ClassName)] -> (ClassName, ClassName) -> Int ->
                    Gen (ClassName, [Field], [(MethodName, [ClassName], ClassName)], ClassName)
genClassP2Typed prevClasses nextClasses (cn, scn) size  = do
  -- TODO figure out sizing and proportions
  let Just (_, superfs, superms, _) = find (\(nm,_,_,_) -> scn == nm) prevClasses
  let allclasses = (1, return $ Name "Object") : fmap (\c -> (5, return c)) (map (\(nm,_,_,_) -> nm) prevClasses ++ [cn] ++ map fst nextClasses)
  (,,,) <$> pure cn
        <*> ((superfs ++) <$> (nub <$> resize (size `div` 3) (listOf (Field <$> frequency allclasses <*> genName))))
        <*> ((superms ++) <$> (nub <$>  resize (size `div` 3) (listOf ((,,) <$> genName <*> resize (size `div` 4) (listOf (frequency allclasses)) <*> frequency allclasses))))
        <*> pure scn

genClassTyped :: CachedProg -> [(ClassName, [Field], [(MethodName, [ClassName], ClassName)], ClassName)] -> Int -> Int -> Gen (Maybe Class)
genClassTyped prevProg classes index size = runMaybeT $ do
  let (cn, fs, ms, sn) = classes !! index
  let cms = map (\(mn, atys, rty) -> (cn, mn, atys, rty)) ms
  let supertypes = foldl' (\prevSupers (c,_,_,sc)  ->
                            let Just scsupers = Map.lookup sc prevSupers
                            in  Map.insert c (sc:scsupers) prevSupers) (Map.singleton (Name "Object") []) classes
  let allcs = map (\(c,fs,_,_) -> (c, map fieldName fs)) classes
  let allfs = concatMap (\(c,fs,_,_) -> map (\f -> (c, fieldName f, fieldType f)) fs) classes
  let allms = concatMap (\(c,_,ms,_) -> map (\(mn, atys, rty) -> (c, mn, atys, rty)) ms) classes
  let Just sfvals = fieldsOf prevProg sn
  let specificfs = fs \\ sfvals
  Class cn sn specificfs (Constructor fs sfvals) <$>
    mapM (\m -> MaybeT $ genMethodTyped supertypes allcs allfs allms m ((max 0 $ size - length specificfs) `div` length cms)) cms

genMethodTyped :: Map ClassName [ClassName] -> [(ClassName, [ClassName])] -> [(ClassName, FieldName, ClassName)] -> [(ClassName, MethodName, [ClassName], ClassName)] -> (ClassName, MethodName, [ClassName], ClassName) -> Int -> Gen (Maybe Method)
genMethodTyped supertypes constructors fields methods (mclass, methodnm, argtys, retty) size = runMaybeT $ do
    params <- Trans.lift (zip argtys <$> (vectorOf (length argtys) ((Name . getReadable) <$> arbitrary) `suchThat` unique))
    body <- MaybeT (join <$> (genExprTyped supertypes constructors fields methods (params ++ [(mclass, Name "this")]) Nothing retty size `suchThatMaybe` isJust)) -- Try with some backtracking
    return $ Method retty methodnm params body

genExprTyped :: Map ClassName [ClassName] -> [(ClassName, [ClassName])] -> [(ClassName, FieldName, ClassName)] -> [(ClassName, MethodName, [ClassName], ClassName)] -> [(ClassName, Name)] -> Maybe ClassName -> ClassName -> Int -> Gen (Maybe Expr)
genExprTyped supertypes constructors fields methods env = go
  where go :: Maybe ClassName -> ClassName -> Int -> Gen (Maybe Expr)
        go targetSubType targetSuperType size =
            if not (null possibleValues) then
              oneof possibleValues
            else return Nothing
          where possibleValues = [(Just . Var Nothing . snd) <$> elements possibleVars | not (null possibleVars)] ++
                                 [runMaybeT $ do
                                       (tty, fnm, _fty) <- Trans.lift $ elements possibleFields
                                       texpr <- MaybeT $ go Nothing tty (size - 1)
                                       return $ FieldAccess Nothing texpr fnm
                                     | not (null possibleFields) && size > 0 ] ++
                                 [runMaybeT $ do
                                       (tty, mnm, atys, _retty) <- Trans.lift $ elements possibleMethods
                                       let size' = size `div` (length atys + 1)
                                       texpr <- MaybeT $ go Nothing tty size'
                                       aexprs <- mapM (MaybeT . flip (go Nothing) size') atys
                                       return $ MethodCall Nothing texpr mnm aexprs
                                     | not (null possibleMethods) && size > 0] ++
                                 [runMaybeT $ do
                                       (tty, atys) <- Trans.lift $ elements possibleConstructors
                                       let size' = size `div` length atys
                                       aexprs <- mapM (MaybeT . flip (go Nothing) size') atys
                                       return $ New Nothing tty aexprs
                                     | not (null possibleConstructors) && size > 0] ++
                                 [runMaybeT $ do
                                       castTy <- MaybeT $ genType supertypes targetSubType targetSuperType
                                       castExpr <- MaybeT $ go Nothing castTy (size - 1)
                                       return $ Cast Nothing castTy castExpr
                                     | size > 0] ++
                                 [runMaybeT $ do
                                       castTy <- MaybeT $ genType supertypes targetSubType targetSuperType
                                       castExpr <- MaybeT $ go (Just castTy) (Name "Object") (size - 1)
                                       return $ Cast Nothing castTy castExpr
                                     | size > 0]
                possibleConstructors = filter (\(ty, _argtys) -> withinBounds ty) constructors
                possibleFields = filter (\(_ety, _fn, fty) -> withinBounds fty) fields
                possibleMethods = filter (\(_ety, _mn, _argtys, retty) -> withinBounds retty) methods
                possibleVars = filter (\(xty, _xn) -> withinBounds xty) env
                withinBounds ty =
                  any (targetSuperType `elem`) ((ty :) <$> Map.lookup ty supertypes) &&
                      all (\subty -> any (ty `elem`) ((subty :) <$> Map.lookup subty supertypes)) targetSubType

genType :: Map ClassName [ClassName] -> Maybe ClassName -> ClassName -> Gen (Maybe ClassName)
genType supertypes lty hty =
    if not (null possibletys) then
      Just <$> elements possibletys
    else return Nothing
  where hsubtys = Map.keys $ Map.filter (hty `elem`) supertypes
        possibletys = filter (\hsty -> all (hsty `elem`) (lty >>= (`Map.lookup` supertypes))) hsubtys
-- Checking

infixr 6 :=>:

data MethodType = [ClassName] :=>: ClassName
  deriving (Show, Eq)

isSubtype :: CachedProg -> ClassName -> ClassName -> Bool
isSubtype p c1 c2 = c1 == c2 || any (c2 `elem`) (Map.lookup c1 (cchSupertypes p))

fieldsOf :: CachedProg -> ClassName -> Maybe [Field]
fieldsOf p = flip Map.lookup (cchFields p)

methodsOf :: CachedProg -> ClassName -> Maybe [Method]
methodsOf p = flip Map.lookup (cchMethods p)

methodType :: CachedProg -> MethodName -> ClassName -> Maybe MethodType
methodType prog mn cn = do
  mets <- reverse <$> methodsOf prog cn
  m <- find ((== mn) . methodName) mets
  return (map fst (methodParameters m) :=>: methodReturnType m)

methodBody :: CachedProg -> MethodName -> ClassName -> Maybe Expr
methodBody prog mn cn = do
  mets <- reverse <$> methodsOf prog cn
  m <- find ((== mn) . methodName) mets
  return (methodBodyExpr m)

checkScope :: Prog -> Bool
checkScope prog =
  case makeCached prog of
    Just cprog -> all (checkClassScope cprog) (classes prog)
    Nothing    -> False

checkClassScope :: CachedProg -> Class -> Bool
checkClassScope prog (Class cn sn cflds (Constructor iflds sflds) meths) =
     iflds == sflds ++ cflds
  && elem sflds (fieldsOf prog sn)
  && all (checkMethodScope prog) meths

checkMethodScope :: CachedProg -> Method -> Bool
checkMethodScope prog (Method _rty _mnm pars mbody) = checkExpressionScope prog (map snd pars ++ [Name "this"]) mbody

checkExpressionScope :: CachedProg -> [Name] -> Expr -> Bool
checkExpressionScope _prog env (Var Nothing nm)           = nm `elem` env
checkExpressionScope prog env (FieldAccess Nothing e f)   =
  checkExpressionScope prog env e && any ((== f) . fieldName) (concat . Map.elems . cchFields $ prog)
checkExpressionScope prog env (MethodCall Nothing e m es) =
   checkExpressionScope prog env e &&
   any (\m' -> length (methodParameters m') == length es && ((== m) . methodName $ m'))
       (concat . Map.elems . cchMethods $ prog) &&
   all (checkExpressionScope prog env) es
checkExpressionScope prog env (New Nothing c es)          = length (let Just fs = fieldsOf prog c in fs) == length es && all (checkExpressionScope prog env) es
checkExpressionScope prog env (Cast Nothing _c e)         = checkExpressionScope prog env e
checkExpressionScope prog env _                           = False

checkTypes :: CachedProg -> Maybe CachedProg
checkTypes prog = makeCached =<< (Prog <$> mapM (checkClassType prog) (classes . cchProg $ prog))

checkClassType :: CachedProg -> Class -> Maybe Class
checkClassType prog (Class cn sn cflds (Constructor iflds sflds) meths) = do
     guard $ iflds == sflds ++ cflds
     guard $ elem sflds (fieldsOf prog sn)
     meths' <- mapM (checkMethodType prog cn) meths
     return (Class cn sn cflds (Constructor iflds sflds) meths')

checkMethodType :: CachedProg -> ClassName -> Method -> Maybe Method
checkMethodType prog cn (Method rty mnm pars mbody) = do
  csuper:_ <- Map.lookup cn (cchSupertypes prog)
  guard $ all (\(sparty :=>: srty) -> map fst pars == sparty && rty == srty) (methodType prog mnm csuper)
  (bodyty, mbody') <- typeExpression prog (pars ++ [(cn, Name "this")]) mbody
  guard $ isSubtype prog bodyty rty
  return $ Method rty mnm pars mbody'

typeExpression :: CachedProg -> [(ClassName, Name)] -> Expr -> Maybe (ClassName, Expr)
-- a pair of result type and type-annotated expression
typeExpression prog env (Var Nothing x) =
  let xty = lookup x (map swap env)
  in (,) <$> xty <*> return (Var xty x)
typeExpression prog env (FieldAccess Nothing e0 fi) = do
  (e0ty, e0') <- typeExpression prog env e0
  fs  <- fieldsOf prog e0ty
  fty <- fieldType <$> find ((== fi) . fieldName) fs
  return (fty, FieldAccess (Just fty) e0' fi)
typeExpression prog env (MethodCall Nothing e0 m es) = do
  (e0ty, e0') <- typeExpression prog env e0
  (parstys :=>: mrety) <- methodType prog m e0ty
  guard $ length es == length parstys
  (ets, es') <- unzip <$> mapM (typeExpression prog env) es
  guard $ all (uncurry (isSubtype prog)) (zip ets parstys)
  return (mrety, MethodCall (Just mrety) e0' m es')
typeExpression prog env (New Nothing cn es) = do
  fts <- map fieldType <$> fieldsOf prog cn
  guard $ length es == length fts
  (ets, es') <- unzip <$> mapM (typeExpression prog env) es
  guard $ all (uncurry (isSubtype prog)) (zip ets fts)
  return (cn, New (Just cn) cn es')
typeExpression prog env (Cast Nothing tc e) = do
  (_ety, e') <- typeExpression prog env e
  return {-
    if not (isSubtype prog ety tc) && not (isSubtype prog tc ety)
    then tc {- STUPID WARNING -}
    else -} (tc, Cast (Just tc) tc e')
typeExpression _prog _env _ = Nothing

forgetTypeAnnotations :: Prog -> Prog
forgetTypeAnnotations = transformBi (\(e :: Expr) -> e { exprType = Nothing })

-- Pretty Printing
prettyProg :: Prog -> Doc
prettyProg = vcat . map prettyClass . classes

prettyClass :: Class -> Doc
prettyClass (Class cn sn fs ctor ms) =
  text "class" <+> text (unName cn) <+> text "extends" <+> text (unName sn) <+> lbrace $+$
  nest 2 (vcat (map prettyField fs ++ [prettyConstructor cn ctor fs] ++ map prettyMethod ms)) $+$
  rbrace

prettyField :: Field -> Doc
prettyField (Field cn fn) = text (unName cn) <+> text (unName fn) <> semi

prettyConstructor :: ClassName -> Constructor -> [Field] -> Doc
prettyConstructor cn (Constructor args superargs) fs =
     text (unName cn) <> parens (sep $ punctuate comma (map prettyArg args)) <+> lbrace $+$
     nest 2 (vcat $ (text "super" <> parens (sep $ punctuate comma (map (text . unName . fieldName) superargs)) <> semi) :
                    map prettyInitialize fs) $+$
     rbrace
  where prettyArg :: Field -> Doc
        prettyArg (Field cn fn) = text (unName cn) <+> text (unName fn)
        prettyInitialize :: Field -> Doc
        prettyInitialize (Field cn fn) = text "this" <> text "." <> text (unName fn) <+> equals <+> text (unName fn) <> semi

prettyMethod :: Method -> Doc
prettyMethod (Method rty mnm pars body) =
    text (unName rty) <+> text (unName mnm) <> parens (sep $ punctuate comma (map prettyPar pars)) <+> lbrace $+$
    nest 2 (text "return" <+> prettyExpr body <> semi) $+$
    rbrace
  where prettyPar :: (ClassName, Name) -> Doc
        prettyPar (cn, n) = text (unName cn) <+> text (unName n)

prettyExpr :: Expr -> Doc
prettyExpr (Var _ nm) = text (unName nm)
prettyExpr (FieldAccess _ e f) = prettyExpr e <> text "." <> text (unName f)
prettyExpr (MethodCall _ e0 m es) = prettyExpr e0 <> text "." <> text (unName m) <> parens (sep $ punctuate comma (map prettyExpr es))
prettyExpr (New _ c es) = text "new" <+> text (unName c) <> parens (sep $ punctuate comma (map prettyExpr es))
prettyExpr (Cast _ c e) = parens (text (unName c)) <> prettyExpr e

-- Refactorings
findClass :: (MonadError String m) => Prog -> ClassName -> m Class
findClass prog classnm =  fromMaybe (throwError $ "Unknown class: " ++ unName classnm)
                                    (return <$> find ((== classnm) . className) (classes prog))


renameFieldPrecondition :: (MonadError String m) => CachedProg -> ClassName -> FieldName -> FieldName -> m ()
renameFieldPrecondition prog classnm oldfieldnm newfieldnm = do
  class'      <- findClass (cchProg prog) classnm
  unless (any ((== oldfieldnm) . fieldName) $ fields class') $
        throwError ("Class " ++ unName classnm ++ "does not have field " ++ unName oldfieldnm)
  when   (any (any ((== newfieldnm) . fieldName)) $ fieldsOf prog classnm) $
        throwError ("Class " ++ unName classnm ++
                  "or one of its superclasses already have field " ++ unName newfieldnm)


renameField :: (MonadError String m) => CachedProg -> ClassName -> FieldName -> FieldName -> m Prog
renameField prog classnm oldfieldnm newfieldnm = do
  renameFieldPrecondition prog classnm oldfieldnm newfieldnm
  let prog' = rewriteBi (\(c :: Class) ->
                            if className c == classnm
                            then do
                              oldField <- find ((== oldfieldnm) . fieldName) (fields c)
                              return c {
                                fields = Field (fieldType oldField) newfieldnm :
                                           delete oldField (fields c),
                                constructor = (constructor c) {
                                                 constructorArguments =
                                                     map (\a -> if fieldName a == oldfieldnm
                                                                then oldField { fieldName = newfieldnm }
                                                                else a) $ constructorArguments (constructor c)
                                                            }
                                }
                            else Nothing) (cchProg prog)
  return $ rewriteBi (\(e :: Expr) ->
                        case e of
                          FieldAccess (Just c) e f ->
                            if isSubtype prog c classnm && f == oldfieldnm
                            then return $ FieldAccess (Just c) e newfieldnm
                            else Nothing
                          _ -> Nothing) prog'


extractSuperPrecondition :: (MonadError String m) => CachedProg -> ClassName -> ClassName -> ClassName -> m (Class, Class)
extractSuperPrecondition prog class1nm class2nm newsupernm = do
  class1 <- findClass (cchProg prog) class1nm
  class2 <- findClass (cchProg prog) class2nm
  unless (superclass class1 == superclass class2) $
    throwError $ "The provided classes " ++ unName class1nm ++ " and " ++
                   unName class2nm ++ " do not have the same supertype"
  when (Set.member newsupernm . Map.keysSet $ cchSupertypes prog) $
    throwError $ "Target superclass name, " ++ unName newsupernm ++ " is already in use"
  return (class1, class2)

extractSuper :: (MonadError String m) => CachedProg -> ClassName -> ClassName -> ClassName -> m Prog
extractSuper prog class1nm class2nm newsupernm = do
  (class1, class2) <- extractSuperPrecondition prog class1nm class2nm newsupernm
  let commonFields  = fields class1 `intersect` fields class2
  let commonMethods = methods class1 `intersect` methods class2
  let prevsupernm     = superclass class1
  prevsuperfields <- fromMaybe (throwError $ "Can not find fields of " ++ unName prevsupernm)
                               (return <$> fieldsOf prog prevsupernm)
  let prog' = rewriteBi (\(c :: Class) ->
                           if (className c == class1nm || className c == class2nm) && superclass c /= newsupernm
                           then
                             let newfields = fields c \\ commonFields
                                 newmethods = methods c \\ commonMethods
                                 newsuperfields = prevsuperfields ++ commonFields
                             in return c {
                                  fields = newfields,
                                  methods = newmethods,
                                  constructor = Constructor (newsuperfields ++ newfields) newsuperfields,
                                  superclass = newsupernm }
                           else Nothing) (cchProg prog)
  let prog'' = prog' { classes = Class newsupernm prevsupernm commonFields
                                       (Constructor (prevsuperfields ++ commonFields) prevsuperfields) commonMethods :
                                         classes prog' }
  -- TODO Extend extract superclass to handle generalization of function parameters and other local variables where possible
  return prog''

replaceDelegationWithInheritancePrecondition :: (MonadError String m) => CachedProg -> ClassName -> FieldName -> m (Class, Field)
replaceDelegationWithInheritancePrecondition prog classnm fieldnm = do
  class' <- findClass (cchProg prog) classnm
  unless (superclass class' == Name "Object") $
    throwError $ "Class " ++ unName classnm ++ " already has a superclass " ++ unName (superclass class')
  field <- fromMaybe (throwError $ "Class " ++ unName classnm ++ " does not contain field " ++ unName fieldnm)
                     (return <$> find ((== fieldnm) . fieldName) (fields class'))
  when (isSubtype prog (fieldType field) (className class')) $
    throwError $ "Target type of field " ++ unName (fieldName field) ++ " must not be a subtype of target class" ++ unName (className class')
  return (class', field)

replaceDelegationWithInheritance :: (MonadError String m) => CachedProg -> ClassName -> FieldName -> m Prog
replaceDelegationWithInheritance prog classnm fieldnm = do
  (class', field) <- replaceDelegationWithInheritancePrecondition prog classnm fieldnm
  let fty = fieldType field
  ftyfields  <- fromMaybe (throwError $ "Can not find fields of " ++ unName fty)
                          (return <$> fieldsOf prog fty)
  ftymethods <- fromMaybe (throwError $ "Can not find methods of " ++ unName fty)
                          (return <$> methodsOf prog fty)
  let prog' = rewriteBi (\(c :: Class) ->
                           if className c == classnm && elem field (fields c)
                           then
                             let delegatedmethods = filter (\(m :: Method) ->
                                                        any ((== methodName m) . methodName) ftymethods &&
                                                          case methodBodyExpr m of
                                                            (MethodCall (Just _cm) (FieldAccess (Just _cf) (Var (Just _ct) (Name "this")) fn) mn es) ->
                                                              methodName m == mn && fieldnm == fn
                                                            _ -> False
                                                      ) (universeBi c)
                                 newfields = delete field (fields c)
                                 c' = c {
                                      methods = methods c \\ delegatedmethods,
                                      fields = newfields,
                                      constructor = Constructor (ftyfields ++ newfields) ftyfields,
                                      superclass = fty }
                                 c'' = rewriteBi (\(e :: Expr) ->
                                             case e of
                                               FieldAccess (Just _cf) v@(Var (Just _ct) (Name "this")) fn | fieldnm == fn -> return v
                                               _ -> Nothing) c'
                             in return c''
                           else Nothing) (cchProg prog)
  let prog'' = rewriteBi (\(e :: Expr) ->
                            case e of
                              FieldAccess (Just _tc) e fn
                                | Just ety <- exprType e, isSubtype prog ety classnm && fieldnm == fn -> return e
                              _ -> Nothing) prog'
  return prog''

-- Example Programs

animalProg :: Prog
animalProg = Prog [
  Class (Name "Animal") (Name "Object") [Field (Name "Object") (Name "happiness")]
        (Constructor [Field (Name "Object") (Name "happiness")] [])
        [Method (Name "Object") (Name "friend") [(Name "Animal", Name "other")]
                (FieldAccess Nothing (Var Nothing (Name "other")) (Name "happiness"))]
  ]

renamedHappiness :: Prog
renamedHappiness =
  let Just animalProgCached   = makeCached animalProg
      Just animalProgTyped    = checkTypes animalProgCached
      Right animalProgRenamed = renameField animalProgTyped (Name "Animal") (Name "happiness") (Name "excitement")
  in animalProgRenamed

accountProg :: Prog
accountProg = Prog [
      Class (Name "SuperSavingsAccount") (Name "Object")
            [Field (Name "Object") (Name "interest"),
            Field (Name "Object") (Name "balance")]
            (Constructor [Field (Name "Object") (Name "interest"),
                          Field (Name "Object") (Name "balance")] [])
            [Method (Name "SuperSavingsAccount") (Name "updateInterest") [(Name "Object", Name "newInterest")]
                                                (New Nothing (Name "SuperSavingsAccount") [Var Nothing (Name "newInterest"),
                                                                                            FieldAccess Nothing (Var Nothing (Name "this")) (Name "balance")])]
    , Class (Name "BasicAccount") (Name "Object")
            [Field (Name "Object") (Name "balance")]
            (Constructor [Field (Name "Object") (Name "balance")] [])
            []
  ]

extractAccountSuperProg :: Prog
extractAccountSuperProg =
  let Just accountProgCached = makeCached accountProg
      Just accountProgTyped = checkTypes accountProgCached
      Right accountProgSuperExtracted = extractSuper accountProgTyped (Name "SuperSavingsAccount") (Name "BasicAccount") (Name "Account")
  in accountProgSuperExtracted

teacherProg :: Prog
teacherProg = Prog [
   Class (Name "Person") (Name "Object") [Field (Name "Object") (Name "name")]
         (Constructor [Field (Name "Object") (Name "name")] [])
         [Method (Name "Object") (Name "getName") [] (FieldAccess Nothing (Var Nothing (Name "this")) (Name "name"))],
   Class (Name "Teacher") (Name "Object") [Field (Name "Person") (Name "person")]
         (Constructor [Field (Name "Person") (Name "person")] [])
         [Method (Name "Object") (Name "getName") [] (MethodCall Nothing
                                                                 (FieldAccess Nothing (Var Nothing (Name "this")) (Name "person"))
                                                                 (Name "getName") [])]
  ]

teacherInheritanceProg :: Prog
teacherInheritanceProg =
  let Just teacherProgCached = makeCached teacherProg
      Just teacherProgTyped = checkTypes teacherProgCached
      Right teacherProgInheritance = replaceDelegationWithInheritance teacherProgTyped (Name "Teacher") (Name "person")
  in teacherProgInheritance


-- Interface
data TransformationInput a = TransformationInput
            { tiProg :: CachedProg
            , tiAux :: a
            } deriving (Show, Eq)

data Transformation a = Transformation
            { tInputGen :: Gen (Maybe $ TransformationInput a)
            , tPrecond  :: TransformationInput a -> Bool
            , tTrans    :: TransformationInput a -> Maybe Prog
            }


-- Properties

renameFieldInputGen :: Gen (Maybe Prog) -> MaybeT Gen (TransformationInput (ClassName, FieldName, FieldName))
renameFieldInputGen progGen = do
  prog <- MaybeT . fmap join $ progGen `suchThatMaybe`
                      (\(pM :: Maybe Prog) ->
                         any (\p -> any (\cp -> any (\c -> not (null $ fields c)) (classes . cchProg $ cp))
                                        (makeCached p)) pM)
  let Just cp = makeCached prog
  class' <- Trans.lift $ elements (filter (\c -> not (null $ fields c)) (classes . cchProg $ cp))
  oldfield <- Trans.lift (fieldName <$> elements (fields class'))
  newfield <- (Name . getReadable) <$> (MaybeT $ arbitrary `suchThatMaybe` (\(Readable n) -> any (Name n `notElem`) $
                                                               fmap (map fieldName) (fieldsOf cp (className class'))))
  return $ TransformationInput cp (className class', oldfield, newfield)

renameFieldTransformation :: Transformation (ClassName, FieldName, FieldName)
renameFieldTransformation = Transformation
  { tInputGen = runMaybeT $ renameFieldInputGen (sized genProgramTyped)
  , tPrecond = \(TransformationInput prog (cn, ofn, nfn)) -> isRight (renameFieldPrecondition prog cn ofn nfn)
  , tTrans = \(TransformationInput prog (cn, ofn, nfn)) -> either (const Nothing) Just $ renameField prog cn ofn nfn
  }

extractSuperInputGen :: Gen (Maybe Prog) -> MaybeT Gen (TransformationInput (ClassName, ClassName, ClassName))
extractSuperInputGen progGen = do
  prog <- MaybeT . fmap join $ progGen `suchThatMaybe`
                        (\(pM :: Maybe Prog) ->
                           any (\p ->
                            isJust (makeCached p) &&
                              any (\(c1, c2) -> superclass c1 == superclass c2)
                                  [(c1, c2) | c1 <- classes p, c2 <- classes p, className c1 /= className c2 ]) pM)
  (c1,c2) <- Trans.lift $ elements [(c1, c2) | c1 <- classes prog
                                             , c2 <- classes prog
                                             , className c1 /= className c2
                                             , superclass c1 == superclass c2]
  csuper <- (Name . getReadable) <$> (MaybeT $ arbitrary `suchThatMaybe` (\(Readable n) -> Name n `notElem` map className (classes prog)))
  return $ TransformationInput (fromJust . makeCached $ prog) (className c1, className c2, csuper)

extractSuperTransformation :: Transformation (ClassName, ClassName, ClassName)
extractSuperTransformation = Transformation
  { tInputGen = runMaybeT $ extractSuperInputGen (sized genProgramTyped)
  , tPrecond = \(TransformationInput prog (cn1, cn2, cnsuper)) -> isRight (extractSuperPrecondition prog cn1 cn2 cnsuper)
  , tTrans = \(TransformationInput prog (cn1, cn2, cnsuper)) -> either (const Nothing) Just $ extractSuper prog cn1 cn2 cnsuper
  }

replaceDelegationWithInheritanceInputGen :: Gen (Maybe Prog) -> MaybeT Gen (TransformationInput (ClassName, FieldName))
replaceDelegationWithInheritanceInputGen progGen = do
      prog <- MaybeT . fmap join $ progGen `suchThatMaybe`
                        (\(pM :: Maybe Prog) ->
                           any (\p ->
                            let cp = makeCached p
                            in isJust cp &&
                                any (\c -> any
                                      (isRight . replaceDelegationWithInheritancePrecondition (fromJust cp) (className c) .
                                                      fieldName) (fields c)) (classes . cchProg $ fromJust cp)) pM)
      let Just cprog = makeCached prog
      class' <- Trans.lift $ elements (filter
                            (\c -> any
                              (isRight . replaceDelegationWithInheritancePrecondition cprog (className c) .
                                  fieldName) (fields c)) (classes . cchProg $ cprog))
      field <-  Trans.lift $ elements (filter (isRight . replaceDelegationWithInheritancePrecondition cprog (className class') .
                                  fieldName) $ fields class')
      return $ TransformationInput cprog (className class', fieldName field)


replaceDelegationWithInheritanceTransformation :: Transformation (ClassName, FieldName)
replaceDelegationWithInheritanceTransformation = Transformation
  { tInputGen = runMaybeT $ replaceDelegationWithInheritanceInputGen (sized genProgramTyped)
  , tPrecond = \(TransformationInput prog (cn, fn)) ->
                  isRight (replaceDelegationWithInheritancePrecondition prog cn fn)
  , tTrans = \(TransformationInput prog (cn, fn)) ->
                   either (const Nothing) Just $ replaceDelegationWithInheritance prog cn fn
  }

inputGenPrecondProperty :: Show a => Transformation a -> Property
inputGenPrecondProperty tran =
  forAll (tInputGen tran) (\minp -> isJust minp ==> tPrecond tran (fromJust minp))

wellTypednessProperty :: Show a => Transformation a -> Property
wellTypednessProperty tran =
  forAll (tInputGen tran) (\input ->
    let progTy = checkTypes =<< (tiProg <$> input)
    in isJust input && isJust progTy ==>
         let progOut = tTrans tran (fromJust input) { tiProg = fromJust progTy }
         in isJust (checkTypes <$> (makeCached =<< (forgetTypeAnnotations <$> progOut))))

wellTypednessPropertySC :: Transformation a -> (Prog, a) -> LSC.Property
wellTypednessPropertySC tran (prog, aux) =
  let
    cprog = makeCached prog
    progTy = checkTypes =<< cprog
    tinput = TransformationInput (fromJust cprog) aux
  in
    LSC.lift (isJust progTy) LSC.*&* LSC.lift (tPrecond tran tinput)
      LSC.*=>* let
                 progOut = tTrans tran tinput
               in LSC.lift (isJust (checkTypes <$> (makeCached =<< (forgetTypeAnnotations <$> progOut))))

-- Sampling from Generators

sampleProgGen :: Gen (Maybe Prog) -> IO ()
sampleProgGen progGen = do
  vs <- sample' progGen
  let welltyped = filter (\v -> isJust (v >>= makeCached >>= checkTypes)) vs
  mapM_ (putStrLn . (++ "\n\n\n------------------------------") . show)
    welltyped
  putStrLn ("Generated program count total: " ++ show (length vs) ++ "\n" ++ "Generated program count well-typed: " ++ show (length welltyped))
