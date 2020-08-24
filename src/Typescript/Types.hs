{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Typescript.Types where

import           Control.Applicative
import           Control.Monad.Trans.State
import           Data.Dependent.Sum                        (DSum)
import           Data.Fin                                  (Fin)
import           Data.Foldable
import           Data.Functor.Combinator
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Contravariant.Divisible.Free (Dec(..))
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.HFunctor.Route
import           Data.IntMap                               (IntMap)
import           Data.Kind
import           Data.Map                                  (Map)
import           Data.Proxy
import           Data.SOP                                  (NP(..), NS(..), I(..), K(..))
import           Data.Scientific                           (Scientific, toBoundedInteger)
import           Data.Some                                 (Some)
import           Data.Text                                 (Text)
import           Data.Vec.Lazy                             (Vec)
import           Data.Vector                               (Vector)
import           Data.Void
import           GHC.Generics                              (Generic, (:*:)(..))
import           GHC.TypeLits
import qualified Data.Aeson                                as A
import qualified Data.Aeson.BetterErrors                   as ABE
import qualified Data.SOP                                  as SOP
import qualified Data.SOP.NP                               as NP
import qualified Data.Vec.Lazy                             as Vec
import qualified Data.Vector                               as V
import qualified Prettyprinter                             as PP

data PS f a = forall r. PS
    { psItem       :: f r
    , psParser     :: r -> Either Text a
    , psSerializer :: a -> r
    }

instance Invariant (PS f) where
    invmap f g (PS x h k) = PS x (fmap f . h) (k . g)

instance HFunctor PS where
    hmap f (PS x g h) = PS (f x) g h

instance Inject PS where
    inject x = PS x Right id

data EnumLit = ELString Text | ELNumber Scientific

data TSPrim :: Type -> Type where
    TSBoolean    :: TSPrim Bool
    TSNumber     :: TSPrim Scientific
    TSBigInt     :: TSPrim Integer
    TSString     :: TSPrim Text
    TSEnum       :: Text -> Vec n (Text, EnumLit) -> TSPrim (Fin n)
    TSStringLit  :: Text -> TSPrim ()
    TSNumericLit :: Scientific -> TSPrim ()
    TSBigIntLit  :: Integer    -> TSPrim ()
    TSUnknown    :: TSPrim A.Value
    TSAny        :: TSPrim A.Value
    TSVoid       :: TSPrim ()
    TSUndefined  :: TSPrim ()
    TSNull       :: TSPrim ()
    TSNever      :: TSPrim Void

-- newtype ObjFields as = ObjFields { getObjFields :: NP I as }

-- newtype ObjType n as = ObjType { getObjType :: TSType n (ObjFields as) }

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
    '[]     ++ bs = bs
    (a':as) ++ bs = a':(as ++ bs)

type family Concat (as :: [[k]]) :: [k] where
    Concat '[] = '[]
    Concat (a ': as) = a ++ Concat as

data Iso a b = Iso { iTo :: a -> b, iFrom :: b -> a }

-- data ArrayOf ::

data ListOf f a = forall x. ListOf
    (f x)
    (a -> (forall r. (x -> r -> r) -> r -> r))
    ((forall r. (x -> r -> r) -> r -> r) -> a)

instance Invariant (ListOf f) where
    invmap f g (ListOf x toBuild fromBuild) =
      ListOf x (\xs -> toBuild (g xs)) (\h -> f (fromBuild h))

listOf :: f a -> ListOf f [a]
listOf x = ListOf x
        (\xs cons nil -> foldr cons nil xs)
        (\f -> f (:) [])

instance HFunctor ListOf where
    hmap f (ListOf x g h) = ListOf (f x) g h

interpretListOf
    :: Invariant g
    => (forall x. f x -> g [x])
    -> ListOf f a
    -> g a
interpretListOf f (ListOf x g h) = invmap
    (\xs -> h (\cons nil -> foldr cons nil xs))
    (\y -> g y (:) [])
    (f x)

data TSType :: Type -> Type -> Type where
    TSArray        :: ListOf (TSType n) a -> TSType n a
    TSTuple        :: PreT Ap (TSType n) a -> TSType n a
    TSObject       :: PreT Ap (K Text :*: TSType n) a -> TSType n a
    TSUnion        :: PostT Dec (TSType n) a -> TSType n a
    TSNamed        :: n -> TSType n a -> TSType n a
    -- hmm...
    TSIntersection :: PreT Ap (TSType n) a -> TSType n a
    TSPrimType     :: PS TSPrim a -> TSType n a

ppScientific :: Scientific -> PP.Doc x
ppScientific n = maybe (PP.pretty (show n)) PP.pretty
               . toBoundedInteger @Int
               $ n

ppEnumLit :: EnumLit -> PP.Doc x
ppEnumLit = \case
    ELString t -> PP.pretty (show t)
    ELNumber n -> ppScientific n

ppPrim :: TSPrim a -> PP.Doc x
ppPrim = \case
    TSBoolean      -> "boolean"
    TSNumber       -> "number"
    TSBigInt       -> "bigint"
    TSString       -> "string"
    TSEnum n es    -> PP.fillSep
      [ "enum"
      , PP.pretty n
      , PP.encloseSep "{" "}" ","
          [ PP.pretty e PP.<+> ppEnumLit x
          | (e, x) <- toList es
          ]
      ]
    TSStringLit t  -> PP.pretty (show t)
    TSNumericLit n -> ppScientific n
    TSBigIntLit n  -> PP.pretty n
    TSUnknown      -> "unknown"
    TSAny          -> "any"
    TSVoid         -> "void"
    TSUndefined    -> "undefined"
    TSNull         -> "null"
    TSNever        -> "never"

ppType
    :: TSType Void a
    -> PP.Doc x
ppType = \case
    TSArray t   -> getConst (interpretListOf (Const . ppType) t) PP.<+> "[]"
    TSTuple ts  -> PP.encloseSep "[" "]" ", " (icollect ppType ts)
    TSObject ts -> PP.encloseSep "{" "}" "," $
      icollect (\(K n :*: x) -> PP.pretty n PP.<+> ": " PP.<+> ppType x) ts
    TSUnion ts  -> PP.encloseSep "" "" " | " (icollect ppType ts)
    TSNamed v _ -> absurd v
    TSIntersection ts  -> PP.encloseSep "" "" " & " (icollect ppType ts)
    -- TSIntersection ts -> PP.encloseSep "" "" " & " (icollect (ppType . getObjType) ts)
    TSPrimType PS{..} -> ppPrim psItem

enumLitToValue :: EnumLit -> A.Value
enumLitToValue = \case
    ELString t -> A.String t
    ELNumber n -> A.Number n

primToValue :: TSPrim a -> a -> A.Value
primToValue = \case
    TSBoolean -> A.Bool
    TSNumber  -> A.Number
    -- hm...
    TSBigInt  -> A.Number . fromIntegral
    TSString  -> A.String
    TSEnum _ e -> \i -> enumLitToValue (snd (e Vec.! i))
    TSStringLit t -> \_ -> A.String t
    TSNumericLit n -> \_ -> A.Number n
    -- hm...
    TSBigIntLit n -> \_ -> A.Number (fromIntegral n)
    TSUnknown -> id
    TSAny -> id
    -- hm...
    TSVoid -> \_ -> A.Null
    TSUndefined -> \_ -> A.Null
    TSNull -> \_ -> A.Null
    TSNever -> absurd

typeToValue
    :: TSType n a -> a -> A.Value
typeToValue = \case
    TSArray ts  -> A.Array
                 . V.fromList
                 . getOp (interpretListOf (\t -> Op (map (typeToValue t))) ts)
    TSTuple ts  -> A.Array
                 . V.fromList
                 . getOp (preDivisibleT (\t -> Op $ \x -> [typeToValue t x]) ts)
    TSObject ts -> A.object
                 . getOp (preDivisibleT (\(K k :*: t) -> Op $ \x -> [k A..= typeToValue t x]) ts)
    TSUnion ts  -> iapply typeToValue ts
    TSNamed _ t -> typeToValue t
    -- hm...
    TSIntersection ts ->
                   undefined
                 . getOp (preDivisibleT (\t -> Op $ \x -> [typeToValue t x]) ts)
    TSPrimType PS{..} -> primToValue psItem . psSerializer

data ParseErr = PEInvalidEnum [(Text, EnumLit)]
              | PEInvalidString Text Text
              | PEInvalidNumber Scientific Scientific
              | PEInvalidBigInt Integer Integer
              | PEPrimitive Text
              | PENever

parseEnumLit :: EnumLit -> ABE.Parse () ()
parseEnumLit = \case
    ELString t -> ABE.withText $ eqOrFail (const ()) t
    ELNumber t -> ABE.withScientific $ eqOrFail (const ()) t

eqOrFail :: Eq a => (a -> e) -> a -> a -> Either e ()
eqOrFail e x y
  | x == y    = Right ()
  | otherwise = Left (e y)

parsePrim :: TSPrim a -> ABE.Parse ParseErr a
parsePrim = \case
    TSBoolean   -> ABE.asBool
    TSNumber    -> ABE.asScientific
    TSBigInt    -> ABE.asIntegral
    TSString    -> ABE.asText
    TSEnum _ es -> ABE.mapError (\_ -> PEInvalidEnum (toList es)) $ Vec.ifoldr
      (\i (_, e) ps -> (i <$ parseEnumLit e) ABE.<|> ps)
      (ABE.throwCustomError ())
      es
    TSStringLit t -> ABE.withText $ eqOrFail (PEInvalidString t) t
    TSNumericLit t -> ABE.withScientific $ eqOrFail (PEInvalidNumber t) t
    TSBigIntLit t -> ABE.withIntegral $ eqOrFail (PEInvalidBigInt t) t
    TSUnknown -> ABE.asValue
    TSAny -> ABE.asValue
    TSVoid -> ABE.asNull
    TSUndefined -> ABE.asNull
    TSNull -> ABE.asNull
    TSNever -> ABE.throwCustomError PENever

parseType
    :: TSType n a
    -> ABE.Parse ParseErr a
parseType = \case
    TSArray ts -> unwrapFunctor $ interpretListOf (WrapFunctor . ABE.eachInArray . parseType) ts
    TSTuple ts -> flip evalStateT 0 $ (`interpret` ts) $ \t -> StateT $ \i ->
      (,i+1) <$> ABE.nth i (parseType t)
    TSObject ts -> (`interpret` ts) $ \(K k :*: t) -> ABE.key k (parseType t)
    TSUnion ts -> foldr @[] (ABE.<|>) (ABE.throwCustomError PENever) $
        icollect (interpretPost parseType) (unPostT ts)
    TSNamed _ t -> parseType t
    -- hm...
    TSIntersection ts -> interpret parseType ts
    TSPrimType PS{..} -> either (ABE.throwCustomError . PEPrimitive) pure . psParser
                     =<< parsePrim psItem

npToList :: (forall x. f x -> b) -> NP f as -> [b]
npToList f = \case
    Nil -> []
    x :* xs -> f x : npToList f xs

npToList2 :: (forall x. f x -> g x -> b) -> NP f as -> NP g as -> [b]
npToList2 f = \case
    Nil -> \case
      Nil -> []
    x :* xs -> \case
      y :* ys -> f x y : npToList2 f xs ys

zipPS :: (forall x. f x -> g x -> b) -> NP f as -> NS g as -> b
zipPS f = \case
    Nil -> \case {}
    x :* xs -> \case
      Z y  -> f x y
      S ys -> zipPS f xs ys

appendNP :: NP f as -> NP f bs -> NP f (as ++ bs)
appendNP = \case
    Nil -> id
    x :* xs -> (x :*) . appendNP xs

traverseNP
    :: Applicative h
    => (forall x. f x -> h (g x))
    -> NP f as
    -> h (NP g as)
traverseNP f = \case
    Nil -> pure Nil
    x :* xs -> (:*) <$> f x <*> traverseNP f xs

imapNP
    :: (forall x. (h x -> NS h as) -> f x -> g x)
    -> NP f as
    -> NP g as
imapNP f = \case
    Nil -> Nil
    x :* xs -> f Z x :* imapNP (f . (S .)) xs
