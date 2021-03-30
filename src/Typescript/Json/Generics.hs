{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE IncoherentInstances    #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Typescript.Json.Generics (
  -- * Typeclass-based
    GTSType(..)
  , TSOpts(..)
  , GTSSum(..)
  , GTSProduct(..)
  , GTSTypeF(..)
  , GTSSumF(..)
  , GTSProductF(..)
  , GTSEnum(..)
  , EnumOpts(..)
  , MakeMaybe(..)
  , simpleMakeMaybe
  -- * Default instances
  , ToTSType(..)
  , genericToTSType
  , genericToTSType_
  , genericToTSNamed
  , genericToTSNamed_
  , genericToTSType1
  , genericToTSType1_
  , genericToTSTypeF
  , genericToTSTypeF_
  , genericToTSNamedF
  , genericToTSNamedF_
  , genericNamedEnum
  -- * Util
  , type (++)
  , splitNP
  , mfrom
  , mto
  , MRep
  , MRep1
  , PullMaybe
  , KM1(..)
  -- , Foo(..)
  , FooBar(..)
  , List(..)
  -- , TestType(..)
  ) where

import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Char
import           Data.Default.Class
import           Data.Fin hiding                   (absurd)
import           Data.Foldable
import           Data.Functor.Combinator
import           Data.Functor.Invariant
import           Data.Kind
import           Data.Proxy
import           Data.SOP                          (NP(..), hpure, All, Top)
import           Data.Text                         (Text)
import           Data.Vec.Lazy                     (Vec(..))
import           Data.Void
import           GHC.Generics
import           GHC.TypeLits
import           Type.Reflection
import           Typescript.Json
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators
import qualified Data.Aeson                        as A
import qualified Data.SOP                          as SOP
import qualified Data.Set                          as S
import qualified Data.Text                         as T
import qualified Data.Type.Nat                     as N
import qualified Data.Vec.Lazy                     as Vec
import qualified Unsafe.Coerce                     as Unsafe

class ToTSType a where
    toTSType :: TSType_ p a

    default toTSType :: (Generic a, GTSType (MRep a), All ToTSType (LeafTypes (MRep a))) => TSType_ p a
    toTSType = genericToTSType_ def

instance ToTSType Int where
    toTSType = TSType_ tsBoundedInteger

instance ToTSType Double where
    toTSType = TSType_ tsDouble

instance ToTSType Bool where
    toTSType = TSType_ tsBoolean

instance ToTSType Ordering where
    toTSType = TSType_ $ TSNamedType (genericNamedEnum @Ordering def :$ Nil2)

instance ToTSType Text where
    toTSType = TSType_ tsText

instance ToTSType a => ToTSType [a] where
    toTSType = TSType_ $ tsList toTSType

instance ToTSType a => ToTSType (Maybe a) where
    toTSType = TSType_ $ tsMaybe "none" "some" (toTSType @a)

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
    '[] ++ bs = bs
    (a ': as) ++ bs = a ': (as ++ bs)

genericToTSType_
    :: forall a p.
     ( Generic a, GTSType (MRep a), All ToTSType (LeafTypes (MRep a)) )
    => TSOpts
    -> TSType_ p a
genericToTSType_ tso = genericToTSType @a tso (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSType
    :: forall a p. (Generic a, GTSType (MRep a))
    => TSOpts
    -> NP (TSType_ p) (LeafTypes (MRep a))
    -> TSType_ p a
genericToTSType tso = invmap mto mfrom . gtoTSType @(MRep a) tso

genericToTSNamed_
    :: forall a p. (Typeable a, Generic a, GTSType (MRep a), All ToTSType (LeafTypes (MRep a)))
    => TSOpts
    -> TSNamed_ p '[] '[] a
genericToTSNamed_ tso = genericToTSNamed @a tso (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSNamed
    :: forall a p. (Typeable a, Generic a, GTSType (MRep a))
    => TSOpts
    -> NP (TSType_ p) (LeafTypes (MRep a))
    -> TSNamed_ p '[] '[] a
genericToTSNamed tso@TSOpts{..} =
    tsNamed_ (tsoTypeNameModifier (someTypeRep @_ @a Proxy)) . genericToTSType @a tso

genericToTSType1_
    :: forall f p a. (Typeable f, Generic1 f, GTSTypeF (MRep1 f), All ToTSType (LeafTypes (MRep1 f)))
    => TSOpts
    -> TSType_ p a
    -> TSType_ p (f a)
genericToTSType1_ tso = genericToTSType1 @f tso (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSType1
    :: forall f p a. (Typeable f, Generic1 f, GTSTypeF (MRep1 f))
    => TSOpts
    -> NP (TSType_ p) (LeafTypes (MRep1 f))
    -> TSType_ p a
    -> TSType_ p (f a)
genericToTSType1 tso lts (TSType_ tx) =
    withTSNamed_ (TSType_ . TSNamedType . (:$ (Arg_ (Arg' tx) :** Nil2))) $
      genericToTSNamedF @f tso lts

genericToTSTypeF_
    :: forall f p a. (Generic1 f, GTSTypeF (MRep1 f), All ToTSType (LeafTypes (MRep1 f)))
    => TSOpts
    -> TSTypeF_ p '[a] '[ 'Nothing ] (f a)
genericToTSTypeF_ tso = genericToTSTypeF @f tso (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSTypeF
    :: forall f p a. (Generic1 f, GTSTypeF (MRep1 f))
    => TSOpts
    -> NP (TSType_ p) (LeafTypes (MRep1 f))
    -> TSTypeF_ p '[a] '[ 'Nothing ] (f a)
genericToTSTypeF tso = invmap mto1 mfrom1 . gtoTSTypeF @(MRep1 f) tso

genericToTSNamedF_
    :: forall f p a. (Typeable f, Generic1 f, GTSTypeF (MRep1 f), All ToTSType (LeafTypes (MRep1 f)))
    => TSOpts
    -> TSNamed_ p '[a] '[ 'Nothing ] (f a)
genericToTSNamedF_ tso = genericToTSNamedF tso (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSNamedF
    :: forall f p a. (Typeable f, Generic1 f, GTSTypeF (MRep1 f))
    => TSOpts
    -> NP (TSType_ p) (LeafTypes (MRep1 f))
    -> TSNamed_ p '[a] '[ 'Nothing ] (f a)
genericToTSNamedF tso@TSOpts{..} =
    invmap mto1 mfrom1
  . withTSTypeF_ (TSNamed_ . TSNamed (tsoTypeNameModifier (someTypeRep @_ @f Proxy)) . TSNFunc)
  . gtoTSTypeF @(MRep1 f) tso

newtype KM1 i a x = KM1 { unKM1 :: Maybe a }
  deriving Show

type family PullMaybe (f :: Type -> Type) :: Type -> Type where
    PullMaybe (K1 i (Maybe a)) = KM1 i a
    PullMaybe (K1 i a)   = K1 i a
    PullMaybe U1         = U1
    PullMaybe V1         = V1
    PullMaybe (M1 x y f) = M1 x y (PullMaybe f)
    PullMaybe Par1       = Par1
    PullMaybe (f :+: g)  = PullMaybe f :+: PullMaybe g
    PullMaybe (f :*: g)  = PullMaybe f :*: PullMaybe g

type MRep a = PullMaybe (Rep a)

mfrom :: forall a x. Generic a => a -> MRep a x
mfrom = Unsafe.unsafeCoerce . from @a @x

mto :: forall a x. Generic a => MRep a x -> a
mto = to @a @x . Unsafe.unsafeCoerce

type MRep1 a = PullMaybe (Rep1 a)

mfrom1 :: forall f x. Generic1 f => f x -> MRep1 f x
mfrom1 = Unsafe.unsafeCoerce . from1 @_ @f @x

mto1 :: forall f x. Generic1 f => MRep1 f x -> f x
mto1 = to1 @_ @f @x . Unsafe.unsafeCoerce

type family LeafTypes (f :: Type -> Type) :: [Type] where
    LeafTypes (K1 i a)   = '[a]
    LeafTypes (KM1 i a)  = '[a]
    LeafTypes U1         = '[]
    LeafTypes V1         = '[]
    LeafTypes (M1 x y f) = LeafTypes f
    LeafTypes Par1       = '[]
    LeafTypes (f :+: g)  = LeafTypes f ++ LeafTypes g
    LeafTypes (f :*: g)  = LeafTypes f ++ LeafTypes g

newtype MakeMaybe = MakeMaybe { runMakeMaybe :: forall p a. TSType_ p a -> TSType_ p (Maybe a) }

-- | "none" | { "some": x }
simpleMakeMaybe
    :: T.Text           -- ^ "none" key
    -> T.Text           -- ^ "some" key
    -> MakeMaybe
simpleMakeMaybe n j = MakeMaybe $ TSType_ . tsMaybe n j

data TSOpts = TSOpts
    { tsoFieldModifier :: String -> T.Text
      -- | If 'False', turns all immediate Maybe fields into optional
      -- fields.  If 'True', keeps the field required.
    , tsoPreserveMaybe :: Bool
      -- | Turn a @a@ into a @Maybe a@, used to fill in top-level Maybe
      -- fields or if 'tsoPreserveMaybe' is 'True'.
    , tsoMakeMaybe :: MakeMaybe
      -- | When assigning fields, if a type is nullable (null is
      -- assignable to it, or it's a union where null or undefined is
      -- a member) then turn it into an optional field and strips the type
      -- of nulls.  Note that this will inline any named definitions if the
      -- type is nullable.
    , tsoCollapseNullable :: Bool
    , tsoConstructorModifier :: String -> T.Text
    , tsoSumOpts :: TaggedValueOpts
    , tsoReadOnlyFields :: Mutability
    , tsoTypeNameModifier :: SomeTypeRep -> T.Text
    }

instance Default TSOpts where
    def = TSOpts
        { tsoFieldModifier = T.pack . A.camelTo2 '_'
        , tsoPreserveMaybe = False
        , tsoMakeMaybe = simpleMakeMaybe "none" "some"
        , tsoCollapseNullable = False
        , tsoConstructorModifier = T.pack
        , tsoSumOpts = def
        , tsoReadOnlyFields = Mutable
        , tsoTypeNameModifier = T.pack . filter (not . isSpace) . show
        }

-- makes an anonymous type
class GTSType (f :: Type -> Type) where
    gtoTSType :: TSOpts -> NP (TSType_ p) (LeafTypes f) -> TSType_ p (f x)

instance GTSType f => GTSType (M1 D ('MetaData nm a b c) f) where
    gtoTSType tso lts = invmap M1 unM1 $ gtoTSType tso lts

instance GTSType f => GTSType (M1 S ('MetaSel s a b c) f) where
    gtoTSType tso lts = mapTSType_ (invmap M1 unM1) (gtoTSType @f tso lts)

instance GTSType f => GTSType (M1 C ('MetaCons constr a b) f) where
    gtoTSType tso lts = mapTSType_ (invmap M1 unM1) (gtoTSType @f tso lts)

instance GTSType (K1 i a) where
    gtoTSType _ (lt :* Nil) = invmap K1 unK1 lt

instance GTSType (KM1 i a) where
    gtoTSType TSOpts{..} (TSType_ lt :* Nil) = invmap KM1 unKM1 $
        runMakeMaybe tsoMakeMaybe (TSType_ lt)

instance GTSType U1 where
    gtoTSType _ _ = TSType_ . invmap (const U1) (const ()) $ TSBaseType (inject TSVoid)

instance GTSType V1 where
    gtoTSType _ _ = TSType_ . invmap absurd (\case {}) $ TSBaseType (inject TSNever)

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
        mergeTB (\case L1 x -> Left x; R1 y -> Right y) L1 R1
          (gtsSum @f tso as)
          (gtsSum @g tso bs)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), GTSProduct t f, GTSProduct t g, WrapProduct k t)
      => GTSType (f :*: g) where
    gtoTSType tso lts = TSType_ . wrapProduct $
        (:*:) <$> (gtsProduct @_ @f tso as (\(x :*: _) -> x))
              <*> (gtsProduct @_ @g tso bs (\(_ :*: y) -> y))
      where
        (as, bs) = splitNP (hpure Proxy) lts

class GTSSum (f :: Type -> Type) where
    gtsSum
        :: TSOpts
        -> NP (TSType_ p) (LeafTypes f)
        -> TaggedBranches p (f x)

instance (All Top (LeafTypes f), GTSSum f, GTSSum g) => GTSSum (f :+: g) where
    gtsSum so lts =
        mergeTB (\case L1 x -> Left x; R1 y -> Right y) L1 R1
          (gtsSum @f so as)
          (gtsSum @g so bs)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance {-# OVERLAPS #-} KnownSymbol constr
      => GTSSum (M1 C ('MetaCons constr a b) U1) where
    gtsSum TSOpts{..} _ = emptyTaggedBranch
                (tsoConstructorModifier (symbolVal (Proxy @constr)))
                (M1 U1)

instance (KnownSymbol constr, GTSType f)
      => GTSSum (M1 C ('MetaCons constr a b) f) where
    gtsSum tso@TSOpts{..} lts
                    = invmap M1 unM1
                    . taggedBranch (tsoConstructorModifier (symbolVal (Proxy @constr)))
                    $ gtoTSType @f tso lts

class WrapProduct k t | t -> k where
    wrapProduct :: t p a a -> TSType p k a

instance WrapProduct 'IsObj ObjectProps where
    wrapProduct = tsObject

instance WrapProduct 'NotObj TupleVals where
    wrapProduct = tsTuple


class (forall p b. Applicative (t p b)) => GTSProduct (t :: N.Nat -> Type -> Type -> Type) (f :: Type -> Type) | f -> t where
    gtsProduct  :: TSOpts -> NP (TSType_ p) (LeafTypes f) -> (a -> f x) -> t p a (f x)

instance (All Top (LeafTypes f), GTSProduct t f, GTSProduct t g) => GTSProduct t (f :*: g) where
    gtsProduct tso lts f =
      (:*:) <$> gtsProduct @_ @f tso as ((\(x :*: _) -> x) . f)
            <*> gtsProduct @_ @g tso bs ((\(_ :*: y) -> y) . f)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance KnownSymbol k => GTSProduct ObjectProps (M1 S ('MetaSel ('Just k) a b c) (K1 i r)) where
    gtsProduct TSOpts{..} (lt :* Nil) f = M1 <$>
        keyVal tsoCollapseNullable
            (unM1 . f)
            tsoReadOnlyFields
            (tsoFieldModifier (symbolVal (Proxy @k)))
            (mapTSType_ (invmap K1 unK1) lt)

instance KnownSymbol k => GTSProduct ObjectProps (M1 S ('MetaSel ('Just k) a b c) (KM1 i r)) where
    gtsProduct TSOpts{..} (lt :* Nil) f
      | tsoPreserveMaybe = M1 . KM1 <$>
            keyVal tsoCollapseNullable
                (unKM1 . unM1 . f)
                tsoReadOnlyFields
                (tsoFieldModifier (symbolVal (Proxy @k)))
                (runMakeMaybe tsoMakeMaybe lt)
      | otherwise        = M1 . KM1 <$>
            keyValMay
                (unKM1 . unM1 . f)
                tsoReadOnlyFields
                (tsoFieldModifier (symbolVal (Proxy @k)))
                lt

instance GTSType f => GTSProduct TupleVals (M1 S ('MetaSel 'Nothing a b c) f) where
    gtsProduct tso lts f =  M1 <$> tupleVal (unM1 . f) (gtoTSType @f tso lts)





class GTSTypeF (f :: Type -> Type) where
    gtoTSTypeF :: TSOpts -> NP (TSType_ p) (LeafTypes f) -> TSTypeF_ p '[a] '[ 'Nothing ] (f a)

instance (All Top (LeafTypes f), GTSSumF f, GTSSumF g) => GTSTypeF (f :+: g) where
    gtoTSTypeF tso@TSOpts{..} lts = TSTypeF_ $
        TSGeneric (Param' "T" :** Nil2) $ \rs (Arg_ (Arg' t) :** Nil2) ->
          tsTaggedUnion tsoSumOpts $ mergeTB (\case L1 x -> Left x; R1 y -> Right y) L1 R1
            (gtsSumF @f tso (hmap (mapTSType_ (tsShift rs)) as) t)
            (gtsSumF @g tso (hmap (mapTSType_ (tsShift rs)) bs) t)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), GTSProductF t f, GTSProductF t g, WrapProduct k t) => GTSTypeF (f :*: g) where
    gtoTSTypeF tso lts = TSTypeF_ $
        TSGeneric (Param' "T" :** Nil2) $ \r (Arg_ (Arg' t) :** Nil2) ->
          wrapProduct $
            (:*:) <$> gtsProductF @t @f tso (hmap (mapTSType_ (tsShift r)) as) (\(x :*: _) -> x) t
                  <*> gtsProductF @t @g tso (hmap (mapTSType_ (tsShift r)) bs) (\(_ :*: y) -> y) t
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance GTSTypeF f => GTSTypeF (M1 D e f) where
    gtoTSTypeF tso lts = mapTSTypeF_ (invmap M1 unM1) (gtoTSTypeF @f tso lts)

instance GTSTypeF f => GTSTypeF (M1 S ('MetaSel s a b c) f) where
    gtoTSTypeF tso lts = mapTSTypeF_ (invmap M1 unM1) (gtoTSTypeF @f tso lts)

instance GTSTypeF f => GTSTypeF (M1 C ('MetaCons constr a b) f) where
    gtoTSTypeF tso lts = mapTSTypeF_ (invmap M1 unM1) (gtoTSTypeF @f tso lts)

instance GTSTypeF Par1 where
    gtoTSTypeF _ _ = TSTypeF_ $
      TSGeneric (Param' "T" :** Nil2) $ \_ (Arg_ (Arg x _) :** Nil2) ->
        -- TODO: can we do this without TSSingle ...
        onTSType_ id TSSingle (invmap Par1 unPar1 (TSType_ x))

instance GTSTypeF (K1 i x) where
    gtoTSTypeF :: forall p a. ()
        => TSOpts
        -> NP (TSType_ p) '[x]
        -> TSTypeF_ p '[a] '[ 'Nothing ] (K1 i x a)
    gtoTSTypeF _ (TSType_ t :* Nil) = TSTypeF_ $
        TSGeneric (Param' "T" :** Nil2) $ \rs _ ->
          tsShift @_ @p rs $ invmap K1 unK1 t

instance GTSTypeF (KM1 i x) where
    gtoTSTypeF :: forall p a. ()
        => TSOpts
        -> NP (TSType_ p) '[x]
        -> TSTypeF_ p '[a] '[ 'Nothing ] (KM1 i x a)
    gtoTSTypeF TSOpts{..} (lt :* Nil) = TSTypeF_ $
        TSGeneric (Param' "T" :** Nil2) $ \rs _ ->
          case runMakeMaybe tsoMakeMaybe lt of
            TSType_ t -> onTSType_ id TSSingle $
              invmap KM1 unKM1 . TSType_ $ tsShift @_ @p rs t

instance GTSTypeF U1 where
    gtoTSTypeF _ _ = TSTypeF_ $
      TSGeneric (Param' "T" :** Nil2) $ \_ _ ->
        invmap (const U1) (const ()) $ TSBaseType (inject TSVoid)

instance GTSTypeF V1 where
    gtoTSTypeF _ _ = TSTypeF_ $
      TSGeneric (Param' "T" :** Nil2) $ \_ _ ->
        invmap absurd (\case {}) $ TSBaseType (inject TSNever)


class GTSSumF (f :: Type -> Type) where
    gtsSumF
        :: TSOpts
        -> NP (TSType_ p) (LeafTypes f)
        -> TSType p k a
        -> TaggedBranches p (f a)

instance (All Top (LeafTypes f), GTSSumF f, GTSSumF g) => GTSSumF (f :+: g) where
    gtsSumF tso lts t =
        mergeTB (\case L1 x -> Left x; R1 y -> Right y) L1 R1
          (gtsSumF @f tso as t)
          (gtsSumF @g tso bs t)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance {-# OVERLAPS #-} KnownSymbol constr
      => GTSSumF (M1 C ('MetaCons constr a b) U1) where
    gtsSumF TSOpts{..} _ _ = emptyTaggedBranch (tsoConstructorModifier (symbolVal (Proxy @constr))) (M1 U1)

instance (KnownSymbol constr, GTSTypeF f)
      => GTSSumF (M1 C ('MetaCons constr a b) f) where
    gtsSumF tso@TSOpts{..} lts t = withTSTypeF_
      (\tsg -> invmap M1 unM1
             . taggedBranch (tsoConstructorModifier (symbolVal (Proxy  @constr)))
             . TSType_
             $ tsApply tsg (Arg_ (Arg' t) :** Nil2)
      )
      (gtoTSTypeF @f tso lts)

class (forall p b. Applicative (t p b)) => GTSProductF (t :: N.Nat -> Type -> Type -> Type) (f :: Type -> Type) | f -> t where
    gtsProductF
              :: TSOpts
              -> NP (TSType_ p) (LeafTypes f)
              -> (b -> f a)
              -> TSType p k a
              -> t p b (f a)


instance (All Top (LeafTypes f), GTSProductF t f, GTSProductF t g) => GTSProductF t (f :*: g) where
    gtsProductF tso lts f t =
        (:*:) <$> gtsProductF @_ @f tso as ((\(x :*: _) -> x) . f) t
              <*> gtsProductF @_ @g tso bs ((\(_ :*: y) -> y) . f) t
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance KnownSymbol k => GTSProductF ObjectProps (M1 S ('MetaSel ('Just k) a b c) (K1 i r)) where
    gtsProductF TSOpts{..} (lt :* Nil) f _ =
        M1 <$> keyVal tsoCollapseNullable (unM1 . f) tsoReadOnlyFields (tsoFieldModifier (symbolVal (Proxy @k)))
                (invmap K1 unK1 lt)

instance KnownSymbol k => GTSProductF ObjectProps (M1 S ('MetaSel ('Just k) a b c) (KM1 i r)) where
    gtsProductF TSOpts{..} (lt :* Nil) f _
      | tsoPreserveMaybe = M1 . KM1 <$>
            keyVal tsoCollapseNullable
              (unKM1 . unM1 . f)
              tsoReadOnlyFields
              (tsoFieldModifier (symbolVal (Proxy @k)))
              (runMakeMaybe tsoMakeMaybe lt)
      | otherwise        = M1 . KM1 <$>
            keyValMay
                (unKM1 . unM1 . f)
                tsoReadOnlyFields
                (tsoFieldModifier (symbolVal (Proxy @k)))
                lt


instance GTSTypeF f => GTSProductF TupleVals (M1 S ('MetaSel 'Nothing a b c) f) where
    gtsProductF tso lts f t = withTSTypeF_
      (\tsg -> M1 <$> tupleVal (unM1 . f)
                        (TSType_ (tsApply tsg (Arg_ (Arg' t) :** Nil2)))
      )
      (gtoTSTypeF @f tso lts)



data EnumOpts = EnumOpts
    { eoSelector :: String -> Text
    , eoLiteral  :: String -> Maybe EnumLit -- ^ if Nothing, picked from free integers, starting from 0
    }

instance Default EnumOpts where
    def = EnumOpts
        { eoSelector = T.pack
        , eoLiteral  = Just . ELString . T.toUpper . T.pack . A.camelTo2 '_'
        }


genericNamedEnum
    :: forall a p. (Generic a, GTSEnum (Rep a))
    => EnumOpts
    -> TSNamed p 'NotObj '[] '[] a
genericNamedEnum = invmap to from . gtsNamedEnum @(Rep a)

class GTSEnum (f :: Type -> Type) where
    gtsNamedEnum :: EnumOpts -> TSNamed p 'NotObj '[] '[] (f x)

instance (KnownSymbol nm, GTSEnumBranches f) => GTSEnum (M1 D ('MetaData nm a b c) f) where
    gtsNamedEnum EnumOpts{..} = tsEnumWith (knownSymbolText @nm)
        (invmap M1 unM1 (gtsebIso @f))
        (evalState (traverse populate constrVec) initInt)
      where
        constrVec = gtsebVec @f
        seen  = S.fromList
          [ i
          | Just (ELNumber i) <- eoLiteral <$> toList constrVec
          ]
        initInt
          | null seen = 0
          | otherwise = max 0 . (+ 1) . floor . maximum $ seen
        populate :: String -> State Int (Text, EnumLit)
        populate str = do
          lit <- case eoLiteral str of
            Nothing -> findValid
            Just x  -> pure x
          pure (eoSelector str, lit)
        findValid :: State Int EnumLit
        findValid = do
          i <- state $ \i -> (i, i+1)
          let tester = fromIntegral i
          if tester `S.member` seen
            then findValid
            else pure (ELNumber tester)

-- TODO: add the error messages for bad instances
class N.InlineInduction (Cardinality f) => GTSEnumBranches (f :: Type -> Type) where
    type Cardinality f :: N.Nat

    gtsebIso :: FinIso (Cardinality f) (f x)
    gtsebVec :: Vec (Cardinality f) String   -- the constructor name

instance GTSEnumBranches V1 where
    type Cardinality V1 = 'N.Z

    gtsebIso = FinIso
      { fiGet = \case {}
      , fiPut = \case {}
      }
    gtsebVec = VNil

instance (GTSEnumBranches f, GTSEnumBranches g, N.InlineInduction (N.Plus (Cardinality f) (Cardinality g)))
        => GTSEnumBranches (f :+: g) where
    type Cardinality (f :+: g) = N.Plus (Cardinality f) (Cardinality g)

    gtsebIso = FinIso
        { fiGet = either (L1 . fiGet fiF) (R1 . fiGet fiG) . split
        , fiPut = append . (\case L1 x -> Left $ fiPut fiF x; R1 y -> Right $ fiPut fiG y)
        }
      where
        fiF = gtsebIso @f
        fiG = gtsebIso @g
    gtsebVec = gtsebVec @f Vec.++ gtsebVec @g

instance KnownSymbol ctr => GTSEnumBranches (M1 C ('MetaCons ctr p q) U1) where
    type Cardinality (M1 C ('MetaCons ctr p q) U1) = 'N.S 'N.Z

    gtsebIso = FinIso
      { fiGet = \_ -> M1 U1
      , fiPut = \_ -> FZ
      }
    gtsebVec = symbolVal (Proxy @ctr) ::: VNil





knownSymbolText :: forall s. KnownSymbol s => Text
knownSymbolText = T.pack (symbolVal (Proxy @s))

data Foo = Foo
    { foo1 :: Int
    , foo2 :: Bool
    , foo3 :: Int
    , foo4 :: Bool
    }
  deriving Generic

data Bar = Bar1 T.Text | Bar2 Double
  deriving Generic

data FooBar a = FooBar Foo Bar a
  deriving (Generic, Generic1)

data Moobie a = Nothong | Jost a
  deriving (Generic, Generic1)

data List a = LNil | LCons a (List a)
  deriving (Generic, Generic1)

data Natt = ZZ | SS Natt
  deriving Generic

instance ToTSType Foo
instance ToTSType Bar
-- TODO: hey this MRep method is kinda funky because of lal these extra
-- constraints. but maybe that snot too bad bc only for parameterized
-- types, and in that case you should use Rep1 anyway.
-- instance (ToTSType a, GTSType (PullMaybe (K1 R a)), All Top (LeafTypes (PullMaybe (K1 R a))), All ToTSType (LeafTypes (PullMaybe (K1 R a)) ++ '[List a])) => ToTSType (List a)
-- instance ToTSType a => ToTSType (FooBar a) where
--     toTSType = genericToTSType1_ def toTSType
-- instance ToTSType a => ToTSType (Moobie a) where
--     toTSType = genericToTSType1_ def toTSType
-- TODO: make this work?
-- instance ToTSType a => ToTSType (List a) where
--     toTSType = genericToTSType1_ def toTSType


