{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Typescript.Types where

import           Control.Monad.Trans.State
import           Data.Dependent.Sum                        (DSum)
import           Data.Fin                                  (Fin)
import           Data.Foldable
import           Data.Functor.Combinator
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divisible.Free (Dec(..))
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

data PS r a = PS
    { psParser     :: r -> Either Text a
    , psSerializer :: a -> r
    }

-- data TSHaskell =

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

data TSType :: ((Type -> Type) -> Type -> Type) -> Type -> Type -> Type where
    TSArray        :: f (TSType f n) (Vector a) -> TSType f n a
    TSTuple        :: PreT Ap (TSType f n) a -> TSType f n a
    TSObject       :: PreT Ap (K Text :*: TSType f n) a -> TSType f n a
    TSUnion        :: PostT Dec (TSType f n) a -> TSType f n a
    TSNamed        :: n -> TSType f n a -> TSType f n a
    -- -- hmm...
    -- TSIntersection :: NP (ObjType n) as -> TSType n (ObjFields (Concat as))
    TSPrimType     :: f TSPrim a -> TSType f n a

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
    :: Interpret f (AltConst (PP.Doc x))
    => TSType f Void a
    -> PP.Doc x
ppType = \case
    TSArray t   -> iget ppType t PP.<+> "[]"
    TSTuple ts  -> PP.encloseSep "[" "]" ", " (icollect ppType ts)
    TSObject ts -> PP.encloseSep "{" "}" "," $
      icollect (\(K n :*: x) -> PP.pretty n PP.<+> ": " PP.<+> ppType x) ts
    TSUnion ts  -> PP.encloseSep "" "" " | " (icollect ppType ts)
    TSNamed v _ -> absurd v
    -- TSIntersection ts -> PP.encloseSep "" "" " & " (icollect (ppType . getObjType) ts)
    TSPrimType p      -> iget ppPrim p

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
    :: Interpret f (Op A.Value)
    => TSType f n a -> a -> A.Value
typeToValue = \case
    TSArray t   -> A.Array . fmap (typeToValue t)
    -- TSTuple ts  -> A.Array . V.fromList . npToList2 (\t (I x) -> typeToValue t x) ts
    -- TSObject ts -> A.object . npToList2 (\(K k :*: t) (I x) -> k A..= typeToValue t x) ts
    -- TSUnion ts  -> zipPS (\t (I x) -> typeToValue t x) ts
    TSNamed _ t -> typeToValue t
    -- hm...
    -- TSIntersection ts -> A.object
    --                    . npToList2 (\(K k :*: t) (I x) -> k A..= typeToValue t x) (foldObjType (TSIntersection ts))
    --                    . getObjFields
    TSPrimType p -> iapply primToValue p

-- data ParseErr = PEInvalidEnum [(Text, EnumLit)]
--               | PEInvalidString Text Text
--               | PEInvalidNumber Scientific Scientific
--               | PEInvalidBigInt Integer Integer
--               | PENever

-- parseEnumLit :: EnumLit -> ABE.Parse () ()
-- parseEnumLit = \case
--     ELString t -> ABE.withText $ eqOrFail (const ()) t
--     ELNumber t -> ABE.withScientific $ eqOrFail (const ()) t

-- eqOrFail :: Eq a => (a -> e) -> a -> a -> Either e ()
-- eqOrFail e x y
--   | x == y    = Right ()
--   | otherwise = Left (e y)

-- parsePrim :: TSPrim a -> ABE.Parse ParseErr a
-- parsePrim = \case
--     TSBoolean   -> ABE.asBool
--     TSNumber    -> ABE.asScientific
--     TSBigInt    -> ABE.asIntegral
--     TSString    -> ABE.asText
--     TSEnum _ es -> ABE.mapError (\_ -> PEInvalidEnum (toList es)) $ Vec.ifoldr
--       (\i (_, e) ps -> (i <$ parseEnumLit e) ABE.<|> ps)
--       (ABE.throwCustomError ())
--       es
--     TSStringLit t -> ABE.withText $ eqOrFail (PEInvalidString t) t
--     TSNumericLit t -> ABE.withScientific $ eqOrFail (PEInvalidNumber t) t
--     TSBigIntLit t -> ABE.withIntegral $ eqOrFail (PEInvalidBigInt t) t
--     TSUnknown -> ABE.asValue
--     TSAny -> ABE.asValue
--     TSVoid -> ABE.asNull
--     TSUndefined -> ABE.asNull
--     TSNull -> ABE.asNull
--     TSNever -> ABE.throwCustomError PENever

-- parseType :: TSType n a -> ABE.Parse ParseErr a
-- parseType = \case
--     TSArray t  -> V.fromList <$> ABE.eachInArray (parseType t)
--     TSTuple ts -> flip evalStateT 0 $ (`traverseNP` ts) $ \t -> StateT $ \i -> do
--       (,i+1) . I <$> ABE.nth i (parseType t)
--     TSObject ts -> ObjFields <$> traverseNP (\(K k :*: t) -> I <$> ABE.key k (parseType t)) ts
--     TSUnion ts ->
--         foldr (ABE.<|>) (ABE.throwCustomError PENever)
--       . npToList (\(K k) -> k)
--       . imapNP (\i t -> K $ i . I <$> parseType t)
--       $ ts
--     TSNamed _ t -> parseType t
--     TSIntersection ts -> ObjFields <$>
--       traverseNP (\(K k :*: t) -> I <$> ABE.key k (parseType t))
--         (foldObjType (TSIntersection ts))
--     TSPrimType p -> parsePrim p

-- foldObjType :: TSType n (ObjFields as) -> NP (K Text :*: TSType n) as
-- foldObjType = \case
--     TSObject ts -> ts
--     TSNamed _ t -> foldObjType t
--     TSIntersection ts -> case ts of
--       Nil             -> Nil
--       ObjType x :* xs -> appendNP (foldObjType x) (foldObjType (TSIntersection xs))
--     TSPrimType p -> case p of {}

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
