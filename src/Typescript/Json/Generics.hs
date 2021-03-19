{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Typescript.Json.Generics (
  -- * Typeclass-based
    GTSType(..)
  , GTSSum(..)
  , GTSObject(..)
  , GTSTuple(..)
  , GTSTypeF(..)
  , GTSSumF(..)
  , GTSObjectF(..)
  , GTSTupleF(..)
  -- * Default instances
  , ToTSType(..)
  , genericToTSType
  , genericToTSType_
  , genericToTSType1
  , genericToTSType1_
  , genericToTSTypeF
  , genericToTSTypeF_
  -- * Util
  , type (++)
  , splitNP
  , FooBar(..)
  -- , TestType(..)
  ) where

import           Data.Bifunctor
import           Data.Default.Class
import           Data.Functor.Combinator
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Invariant
import           Data.Kind
import           Data.Proxy
import           Data.SOP                          (NP(..), K(..), hpure, All, Top)
import           Data.Text                         (Text)
import           Data.Void
import           GHC.Generics
import           GHC.TypeLits
import           Typescript.Json
import           Typescript.Json.Core
import qualified Data.Aeson                        as A
import qualified Data.SOP                          as SOP
import qualified Data.Text                         as T

class ToTSType a where
    toTSType :: TSType_ p n a

    default toTSType :: (Generic a, GTSType (Rep a), All ToTSType (LeafTypes (Rep a))) => TSType_ p n a
    toTSType = genericToTSType_ def

instance ToTSType Int where
    toTSType = TSType_ tsBoundedInteger

instance ToTSType Double where
    toTSType = TSType_ tsDouble

instance ToTSType Bool where
    toTSType = TSType_ tsBoolean

instance ToTSType Text where
    toTSType = TSType_ tsText

instance ToTSType a => ToTSType [a] where
    toTSType = TSType_ $ tsList toTSType

instance ToTSType a => ToTSType (Maybe a) where
    toTSType = TSType_ $ tsNullable toTSType

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
    '[] ++ bs = bs
    (a ': as) ++ bs = a ': (as ++ bs)

genericToTSType_
    :: forall a p n.
     ( Generic a, GTSType (Rep a), All ToTSType (LeafTypes (Rep a)) )
    => TSOpts
    -> TSType_ p n a
genericToTSType_ tso = genericToTSType @a tso (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSType
    :: forall a p n. (Generic a, GTSType (Rep a))
    => TSOpts
    -> NP (TSType_ p n) (LeafTypes (Rep a))
    -> TSType_ p n a
genericToTSType tso = invmap to from . gtoTSType @(Rep a) tso

genericToTSType1_
    :: forall f p n a. (Generic1 f, GTSTypeF (Rep1 f), All ToTSType (LeafTypes (Rep1 f)))
    => TSOpts
    -> TSType_ p n a
    -> TSType_ p n (f a)
genericToTSType1_ tso = genericToTSType1 @f tso (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSType1
    :: forall f p n a. (Generic1 f, GTSTypeF (Rep1 f))
    => TSOpts
    -> NP (TSType_ p n) (LeafTypes (Rep1 f))
    -> TSType_ p n a
    -> TSType_ p n (f a)
genericToTSType1 tso lts tx = case genericToTSTypeF @f tso lts of
    TSTypeF_ tf -> TSType_ $ TSApplied tf (tx :* Nil)

genericToTSTypeF_
    :: forall f p n a. (Generic1 f, GTSTypeF (Rep1 f), All ToTSType (LeafTypes (Rep1 f)))
    => TSOpts
    -> TSTypeF_ p n '[a] (f a)
genericToTSTypeF_ tso = genericToTSTypeF @f tso (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSTypeF
    :: forall f p n a. (Generic1 f, GTSTypeF (Rep1 f))
    => TSOpts
    -> NP (TSType_ p n) (LeafTypes (Rep1 f))
    -> TSTypeF_ p n '[a] (f a)
genericToTSTypeF tso = invmap to1 from1 . gtoTSTypeF @(Rep1 f) tso

type family LeafTypes (f :: Type -> Type) :: [Type] where
    LeafTypes (K1 i a)   = '[a]
    LeafTypes U1         = '[]
    LeafTypes V1         = '[]
    LeafTypes (M1 x y f) = LeafTypes f
    LeafTypes Par1       = '[]
    LeafTypes (f :+: g)  = LeafTypes f ++ LeafTypes g
    LeafTypes (f :*: g)  = LeafTypes f ++ LeafTypes g

data TSOpts = TSOpts
    { tsoFieldModifier :: String -> T.Text
    , tsoNullableFields :: Bool
    , tsoConstructorModifier :: String -> T.Text
    , tsoSumOpts :: TaggedValueOpts
    }

instance Default TSOpts where
    def = TSOpts
        { tsoFieldModifier = T.pack . A.camelTo2 '_'
        , tsoNullableFields = True
        , tsoConstructorModifier = T.pack
        , tsoSumOpts = def
        }

class GTSType (f :: Type -> Type) where
    gtoTSType :: TSOpts -> NP (TSType_ p n) (LeafTypes f) -> TSType_ p n (f x)

instance (KnownSymbol nm, GTSType f) => GTSType (M1 D ('MetaData nm a b c) f) where
    gtoTSType tso lts = mapTSType_
      (TSNamed (knownSymbolText @nm) . invmap M1 unM1)
      (gtoTSType @f tso lts)

instance GTSType f => GTSType (M1 S ('MetaSel s a b c) f) where
    gtoTSType tso lts = mapTSType_ (invmap M1 unM1) (gtoTSType @f tso lts)

instance GTSType f => GTSType (M1 C ('MetaCons constr a b) f) where
    gtoTSType tso lts = mapTSType_ (invmap M1 unM1) (gtoTSType @f tso lts)

instance GTSType (K1 i a) where
    gtoTSType _ (lt :* Nil) = invmap K1 unK1 lt

instance GTSType U1 where
    gtoTSType _ _ = TSType_ . invmap (const U1) (const ()) $ TSPrimType (inject TSVoid)

instance GTSType V1 where
    gtoTSType _ _ = TSType_ . invmap absurd (\case {}) $ TSPrimType (inject TSNever)

splitNP
    :: NP p as
    -> NP f (as ++ bs)
    -> (NP f as, NP f bs)
splitNP = \case
    Nil     -> (Nil,)
    _ :* ps -> \case
      x :* xs -> first (x :*) (splitNP ps xs)

instance (All Top (LeafTypes f), GTSSum f, GTSSum g) => GTSType (f :+: g) where
    gtoTSType tso@TSOpts{..} lts = TSType_ . tsTaggedUnion tsoSumOpts $
        decide (\case L1 x -> Left x; R1 y -> Right y)
          (gtsSum @f tso as L1)
          (gtsSum @g tso bs R1)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), KnownSymbol k, GTSType f, GTSObject g)
      => GTSType ((M1 S ('MetaSel ('Just k) a b c) f) :*: g) where
    gtoTSType tso lts = TSType_ . tsObject $
        (:*:) <$> (gtsObject @(M1 S ('MetaSel ('Just k) a b c) f) tso as (\(x :*: _) -> x))
              <*> (gtsObject @g tso bs (\(_ :*: y) -> y))
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), GTSType f, GTSTuple g)
      => GTSType ((M1 S ('MetaSel 'Nothing a b c) f) :*: g) where
    gtoTSType _ lts = TSType_ . tsTuple $
        (:*:) <$> gtsTuple @(M1 S ('MetaSel 'Nothing a b c) f) as (\(x :*: _) -> x)
              <*> gtsTuple @g bs (\(_ :*: y) -> y)
      where
        (as, bs) = splitNP (hpure Proxy) lts

class GTSSum (f :: Type -> Type) where
    gtsSum
        :: TSOpts
        -> NP (TSType_ p n) (LeafTypes f)
        -> (f x -> a)
        -> TaggedBranches p n a (f x)

instance (All Top (LeafTypes f), GTSSum f, GTSSum g) => GTSSum (f :+: g) where
    gtsSum so lts f =
        decide (\case L1 x -> Left x; R1 y -> Right y)
          (gtsSum @f so as (f . L1))
          (gtsSum @g so bs (f . R1))
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance {-# OVERLAPS #-} KnownSymbol constr
      => GTSSum (M1 C ('MetaCons constr a b) U1) where
    gtsSum TSOpts{..} _ f = () >$ emptyTaggedBranch (f (M1 U1))
                (tsoConstructorModifier (symbolVal (Proxy @constr)))

instance (KnownSymbol constr, GTSType f)
      => GTSSum (M1 C ('MetaCons constr a b) f) where
    gtsSum tso@TSOpts{..} lts f
                    = contramap unM1
                    . taggedBranch (f . M1) (tsoConstructorModifier (symbolVal (Proxy @constr)))
                    $ gtoTSType @f tso lts

class GTSObject (f :: Type -> Type) where
    gtsObject :: TSOpts -> NP (TSType_ p n) (LeafTypes f) -> (a -> f x) -> ObjectProps p n a (f x)

instance (All Top (LeafTypes f), GTSObject f, GTSObject g) => GTSObject (f :*: g) where
    gtsObject oo lts f =
        (:*:) <$> gtsObject @f oo as ((\(x :*: _) -> x) . f)
              <*> gtsObject @g oo bs ((\(_ :*: y) -> y) . f)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (KnownSymbol k, GTSType f) => GTSObject (M1 S ('MetaSel ('Just k) a b c) f) where
    gtsObject tso@TSOpts{..} lts f = M1 <$>
        keyVal tsoNullableFields
            (unM1 . f)
            (tsoFieldModifier (symbolVal (Proxy @k)))
            (gtoTSType @f tso lts)

class GTSTuple (f :: Type -> Type) where
    gtsTuple :: NP (TSType_ p n) (LeafTypes f) -> (a -> f x) -> TupleVals p n a (f x)

instance (All Top (LeafTypes f), GTSTuple f, GTSTuple g) => GTSTuple (f :*: g) where
    gtsTuple lts f =
      (:*:) <$> gtsTuple @f as ((\(x :*: _) -> x) . f)
            <*> gtsTuple @g bs ((\(_ :*: y) -> y) . f)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance GTSType f => GTSTuple (M1 S ('MetaSel 'Nothing a b c) f) where
    gtsTuple lts f =  M1 <$> tupleVal (unM1 . f) (gtoTSType @f undefined lts)





class GTSTypeF (f :: Type -> Type) where
    gtoTSTypeF :: TSOpts -> NP (TSType_ p n) (LeafTypes f) -> TSTypeF_ p n '[a] (f a)

instance (All Top (LeafTypes f), GTSSumF f, GTSSumF g) => GTSTypeF (f :+: g) where
    gtoTSTypeF tso lts = TSTypeF_ $
        TSGeneric ":+:" SNotObj (K "T" :* Nil) $ \rs (TSType_ t :* Nil) ->
          tsTaggedUnion tvo $ decide (\case L1 x -> Left x; R1 y -> Right y)
            (gtsSumF @f tso (hmap (mapTSType_ (tsShift rs)) as) L1 t)
            (gtsSumF @g tso (hmap (mapTSType_ (tsShift rs)) bs) R1 t)
      where
        tvo = def
          { tvoTagKey      = ""
          , tvoContentsKey = ""
          }
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), KnownSymbol k, GTSTypeF f, GTSObjectF g)
      => GTSTypeF ((M1 S ('MetaSel ('Just k) a b c) f) :*: g) where
    gtoTSTypeF tso lts = TSTypeF_ $
        TSGeneric ":*:" SIsObj (K "T" :* Nil) $ \rs (TSType_ t :* Nil) ->
          tsObject $
            (:*:) <$> gtsObjectF @(M1 S ('MetaSel ('Just k) a b c) f)
                        tso
                        (hmap (mapTSType_ (tsShift rs)) as)
                        (\(x :*: _) -> x)
                        t
                  <*> gtsObjectF @g
                        tso
                        (hmap (mapTSType_ (tsShift rs)) bs)
                        (\(_ :*: y) -> y)
                        t
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), GTSTypeF f, GTSTupleF g)
      => GTSTypeF ((M1 S ('MetaSel 'Nothing a b c) f) :*: g) where
    gtoTSTypeF tso lts = TSTypeF_ $
        TSGeneric ":*:" SNotObj (K "T" :* Nil) $ \rs (TSType_ t :* Nil) ->
          tsTuple $
            (:*:) <$> gtsTupleF @(M1 S ('MetaSel 'Nothing a b c) f)
                        tso
                        (hmap (mapTSType_ (tsShift rs)) as)
                        (\(x :*: _) -> x)
                        t
                  <*> gtsTupleF @g
                        tso
                        (hmap (mapTSType_ (tsShift rs)) bs)
                        (\(_ :*: y) -> y)
                        t
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (KnownSymbol nm, GTSTypeF f) => GTSTypeF (M1 D ('MetaData nm a b c) f) where
    gtoTSTypeF tso lts = mapTSTypeF_
      (\tsg -> invmap M1 unM1 $ tsg { tsgName = knownSymbolText @nm })
      (gtoTSTypeF @f tso lts)

instance GTSTypeF f => GTSTypeF (M1 S ('MetaSel s a b c) f) where
    gtoTSTypeF tso lts = mapTSTypeF_ (invmap M1 unM1) (gtoTSTypeF @f tso lts)

instance GTSTypeF f => GTSTypeF (M1 C ('MetaCons constr a b) f) where
    gtoTSTypeF tso lts = mapTSTypeF_ (invmap M1 unM1) (gtoTSTypeF @f tso lts)

-- TODO: hm....
instance GTSTypeF Par1 where
    gtoTSTypeF _ _ = TSTypeF_ $
      TSGeneric "Par1" SNotObj (K "T" :* Nil) $ \_ (x :* Nil) ->
        onTSType_ id TSSingle (invmap Par1 unPar1 x)

instance GTSTypeF (K1 i x) where
    gtoTSTypeF :: forall p n a. TSOpts -> NP (TSType_ p n) '[x] -> TSTypeF_ p n '[a] (K1 i x a)
    gtoTSTypeF _ (TSType_ t :* Nil) = TSTypeF_ $
        TSGeneric "K1" (tsObjType t) (K "T" :* Nil) $ \rs _ ->
          tsShift @_ @p rs $ invmap K1 unK1 t

instance GTSTypeF U1 where
    gtoTSTypeF _ _ = TSTypeF_ $
      TSGeneric "U1" SNotObj (K "T" :* Nil) $ \_ _ ->
        invmap (const U1) (const ()) $ TSPrimType (inject TSVoid)

instance GTSTypeF V1 where
    gtoTSTypeF _ _ = TSTypeF_ $
      TSGeneric "V1" SNotObj (K "T" :* Nil) $ \_ _ ->
        invmap absurd (\case {}) $ TSPrimType (inject TSNever)


class GTSSumF (f :: Type -> Type) where
    gtsSumF
        :: TSOpts
        -> NP (TSType_ p n) (LeafTypes f)
        -> (f a -> b)
        -> TSType p k n a
        -> TaggedBranches p n b (f a)

instance (All Top (LeafTypes f), GTSSumF f, GTSSumF g) => GTSSumF (f :+: g) where
    gtsSumF tso lts f t = decide (\case L1 x -> Left x; R1 y -> Right y)
        (gtsSumF @f tso as (f . L1) t)
        (gtsSumF @g tso bs (f . R1) t)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance {-# OVERLAPS #-} KnownSymbol constr
      => GTSSumF (M1 C ('MetaCons constr a b) U1) where
    gtsSumF TSOpts{..} _ f _ = () >$ emptyTaggedBranch (f (M1 U1)) (tsoConstructorModifier (symbolVal (Proxy @constr)))

-- | Will "flatten out" objects if possible
instance (KnownSymbol constr, GTSTypeF f)
      => GTSSumF (M1 C ('MetaCons constr a b) f) where
    gtsSumF tso@TSOpts{..} lts f t = withTSTypeF_
      (\tsg -> contramap unM1
             . taggedBranch (f . M1) (tsoConstructorModifier (symbolVal (Proxy  @constr)))
             . TSType_
             $ tsApply tsg (TSType_ t :* Nil)
      )
      (gtoTSTypeF @f tso lts)

class GTSObjectF (f :: Type -> Type) where
    gtsObjectF
        :: TSOpts
        -> NP (TSType_ p n) (LeafTypes f)
        -> (b -> f a)
        -> TSType p k n a
        -> ObjectProps p n b (f a)

instance (All Top (LeafTypes f), GTSObjectF f, GTSObjectF g) => GTSObjectF (f :*: g) where
    gtsObjectF tso lts f t =
        (:*:) <$> gtsObjectF @f tso as ((\(x :*: _) -> x) . f) t
              <*> gtsObjectF @g tso bs ((\(_ :*: y) -> y) . f) t
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (KnownSymbol k, GTSTypeF f) => GTSObjectF (M1 S ('MetaSel ('Just k) a b c) f) where
    gtsObjectF tso@TSOpts{..} lts f t = withTSTypeF_
      (\tsg -> M1 <$> keyVal tsoNullableFields (unM1 . f) (tsoFieldModifier (symbolVal (Proxy @k)))
                        (TSType_ (tsApply tsg (TSType_ t :* Nil)))
      )
      (gtoTSTypeF @f tso lts)

class GTSTupleF (f :: Type -> Type) where
    gtsTupleF :: TSOpts
              -> NP (TSType_ p n) (LeafTypes f)
              -> (b -> f a)
              -> TSType p k n a
              -> TupleVals p n b (f a)

instance (All Top (LeafTypes f), GTSTupleF f, GTSTupleF g) => GTSTupleF (f :*: g) where
    gtsTupleF tso lts f t =
        (:*:) <$> gtsTupleF @f tso as ((\(x :*: _) -> x) . f) t
              <*> gtsTupleF @g tso bs ((\(_ :*: y) -> y) . f) t
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance GTSTypeF f => GTSTupleF (M1 S ('MetaSel 'Nothing a b c) f) where
    gtsTupleF tso lts f t = withTSTypeF_
      (\tsg -> M1 <$> tupleVal (unM1 . f)
                        (TSType_ (tsApply tsg (TSType_ t :* Nil)))
      )
      (gtoTSTypeF @f tso lts)

knownSymbolText :: forall s. KnownSymbol s => Text
knownSymbolText = T.pack (symbolVal (Proxy @s))

data Foo = Foo
    { foo1 :: Int
    , foo2 :: Bool
    }
  deriving Generic

data Bar = Bar1 T.Text | Bar2 Double
  deriving Generic

data FooBar a = FooBar Foo Bar a
  deriving (Generic, Generic1)

data Moobie a = Nothong | Jost a
  deriving (Generic, Generic1)

instance ToTSType Foo
instance ToTSType Bar
instance ToTSType a => ToTSType (FooBar a) where
    toTSType = genericToTSType1_ def toTSType
instance ToTSType a => ToTSType (Moobie a) where
    toTSType = genericToTSType1_ def toTSType
