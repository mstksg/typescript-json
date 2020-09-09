{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
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
import qualified Data.SOP                          as SOP
import qualified Data.Text                         as T

type family WarnIfEq (b :: Ordering) (c :: ErrorMessage) :: Constraint where
    WarnIfEq 'LT c = ()
    WarnIfEq 'EQ c = TypeError c
    WarnIfEq 'GT c = ()

type NotEqSym a b = WarnIfEq (CmpSymbol a b)
                ('Text "Cannot derive instance: constructor and tag value are both "
           ':<>: 'Text a
                )

class ToTSType a where
    toTSType :: TSType_ p n a

    default toTSType :: (Generic a, GTSType "tag" "contents" (Rep a), All ToTSType (LeafTypes (Rep a))) => TSType_ p n a
    toTSType = genericToTSType_ @"tag" @"contents" @a

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
    :: forall tag val a p n.
     ( Generic a, GTSType tag val (Rep a), All ToTSType (LeafTypes (Rep a)) )
    => TSType_ p n a
genericToTSType_ = genericToTSType @tag @val @a (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSType
    :: forall tag val a p n. (Generic a, GTSType tag val (Rep a))
    => NP (TSType_ p n) (LeafTypes (Rep a))
    -> TSType_ p n a
genericToTSType = invmap to from . gtoTSType @tag @val @(Rep a)

genericToTSType1_
    :: forall tag val f p n a. (Generic1 f, GTSTypeF tag val (Rep1 f), All ToTSType (LeafTypes (Rep1 f)))
    => TSType_ p n a
    -> TSType_ p n (f a)
genericToTSType1_ = genericToTSType1 @tag @val @f (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSType1
    :: forall tag val f p n a. (Generic1 f, GTSTypeF tag val (Rep1 f))
    => NP (TSType_ p n) (LeafTypes (Rep1 f))
    -> TSType_ p n a
    -> TSType_ p n (f a)
genericToTSType1 lts tx = case genericToTSTypeF @tag @val @f lts of
    TSTypeF_ tf -> TSType_ $ TSApplied tf (tx :* Nil)

genericToTSTypeF_
    :: forall tag val f p n a. (Generic1 f, GTSTypeF tag val (Rep1 f), All ToTSType (LeafTypes (Rep1 f)))
    => TSTypeF_ p n '[a] (f a)
genericToTSTypeF_ = genericToTSTypeF @tag @val @f (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSTypeF
    :: forall tag val f p n a. (Generic1 f, GTSTypeF tag val (Rep1 f))
    => NP (TSType_ p n) (LeafTypes (Rep1 f))
    -> TSTypeF_ p n '[a] (f a)
genericToTSTypeF = invmap to1 from1 . gtoTSTypeF @tag @val @(Rep1 f)

type family LeafTypes (f :: Type -> Type) :: [Type] where
    LeafTypes (K1 i a)   = '[a]
    LeafTypes U1         = '[]
    LeafTypes V1         = '[]
    LeafTypes (M1 x y f) = LeafTypes f
    LeafTypes Par1       = '[]
    LeafTypes (f :+: g)  = LeafTypes f ++ LeafTypes g
    LeafTypes (f :*: g)  = LeafTypes f ++ LeafTypes g

class GTSType (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtoTSType :: NP (TSType_ p n) (LeafTypes f) -> TSType_ p n (f x)

instance (KnownSymbol nm, GTSType tag val f) => GTSType tag val (M1 D ('MetaData nm a b c) f) where
    gtoTSType lts = mapTSType_
      (TSNamed (knownSymbolText @nm) . invmap M1 unM1)
      (gtoTSType @tag @val @f lts)

instance GTSType tag val f => GTSType tag val (M1 S ('MetaSel s a b c) f) where
    gtoTSType lts = mapTSType_ (invmap M1 unM1) (gtoTSType @tag @val @f lts)

instance GTSType tag val f => GTSType tag val (M1 C ('MetaCons constr a b) f) where
    gtoTSType lts = mapTSType_ (invmap M1 unM1) (gtoTSType @tag @val @f lts)

instance GTSType tag val (K1 i a) where
    gtoTSType (lt :* Nil) = invmap K1 unK1 lt

instance GTSType tag val U1 where
    gtoTSType _ = TSType_ . invmap (const U1) (const ()) $ TSPrimType (inject TSVoid)

instance GTSType tag val V1 where
    gtoTSType _ = TSType_ . invmap absurd (\case {}) $ TSPrimType (inject TSNever)

splitNP
    :: NP p as
    -> NP f (as ++ bs)
    -> (NP f as, NP f bs)
splitNP = \case
    Nil     -> (Nil,)
    _ :* ps -> \case
      x :* xs -> first (x :*) (splitNP ps xs)

instance (All Top (LeafTypes f), KnownSymbol tag, KnownSymbol val, GTSSum tag val f, GTSSum tag val g) => GTSType tag val (f :+: g) where
    gtoTSType lts = TSType_ . tsTaggedUnion tvo $
        decide (\case L1 x -> Left x; R1 y -> Right y)
          (gtsSum @tag @val @f as L1)
          (gtsSum @tag @val @g bs R1)
      where
        tvo = def
          { tvoTagKey      = knownSymbolText @tag
          , tvoContentsKey = knownSymbolText @val
          }
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), KnownSymbol k, GTSType tag val f, GTSObject tag val g)
      => GTSType tag val ((M1 S ('MetaSel ('Just k) a b c) f) :*: g) where
    gtoTSType lts = TSType_ . tsObject $
        (:*:) <$> (gtsObject @tag @val @(M1 S ('MetaSel ('Just k) a b c) f) as (\(x :*: _) -> x))
              <*> (gtsObject @tag @val @g bs (\(_ :*: y) -> y))
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), GTSType tag val f, GTSTuple tag val g)
      => GTSType tag val ((M1 S ('MetaSel 'Nothing a b c) f) :*: g) where
    gtoTSType lts = TSType_ . tsTuple $
        (:*:) <$> gtsTuple @tag @val @(M1 S ('MetaSel 'Nothing a b c) f) as (\(x :*: _) -> x)
              <*> gtsTuple @tag @val @g bs (\(_ :*: y) -> y)
      where
        (as, bs) = splitNP (hpure Proxy) lts

class GTSSum (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsSum
        :: NP (TSType_ p n) (LeafTypes f)
        -> (f x -> a)
        -> TaggedBranches p n a (f x)

instance (All Top (LeafTypes f), GTSSum tag val f, GTSSum tag val g) => GTSSum tag val (f :+: g) where
    gtsSum lts f =
        decide (\case L1 x -> Left x; R1 y -> Right y)
          (gtsSum @tag @val @f as (f . L1))
          (gtsSum @tag @val @g bs (f . R1))
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance {-# OVERLAPS #-} (KnownSymbol constr, NotEqSym tag constr)
      => GTSSum tag conts (M1 C ('MetaCons constr a b) U1) where
    gtsSum _ f = () >$ emptyTaggedBranch (f (M1 U1)) (knownSymbolText @constr)

-- | Will "flatten out" objects if possible
instance (KnownSymbol constr, NotEqSym tag constr, GTSType tag val f)
      => GTSSum tag val (M1 C ('MetaCons constr a b) f) where
    gtsSum lts f = contramap unM1
                 . taggedBranch (f . M1) (knownSymbolText @constr)
                 $ gtoTSType @tag @val @f lts

class GTSObject (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsObject :: NP (TSType_ p n) (LeafTypes f) -> (a -> f x) -> ObjectProps p n a (f x)

instance (All Top (LeafTypes f), GTSObject tag val f, GTSObject tag val g) => GTSObject tag val (f :*: g) where
    gtsObject lts f =
        (:*:) <$> gtsObject @tag @val @f as ((\(x :*: _) -> x) . f)
              <*> gtsObject @tag @val @g bs ((\(_ :*: y) -> y) . f)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (KnownSymbol k, GTSType tag val f) => GTSObject tag val (M1 S ('MetaSel ('Just k) a b c) f) where
    gtsObject lts f = M1 <$> keyVal True (unM1 . f) (knownSymbolText @k) (gtoTSType @tag @val @f lts)

class GTSTuple (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsTuple :: NP (TSType_ p n) (LeafTypes f) -> (a -> f x) -> TupleVals p n a (f x)

instance (All Top (LeafTypes f), GTSTuple tag val f, GTSTuple tag val g) => GTSTuple tag val (f :*: g) where
    gtsTuple lts f =
      (:*:) <$> gtsTuple @tag @val @f as ((\(x :*: _) -> x) . f)
            <*> gtsTuple @tag @val @g bs ((\(_ :*: y) -> y) . f)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance GTSType tag val f => GTSTuple tag val (M1 S ('MetaSel 'Nothing a b c) f) where
    gtsTuple lts f =  M1 <$> tupleVal (unM1 . f) (gtoTSType @tag @val @f lts)







class GTSTypeF (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtoTSTypeF :: NP (TSType_ p n) (LeafTypes f) -> TSTypeF_ p n '[a] (f a)

instance (All Top (LeafTypes f), KnownSymbol tag, KnownSymbol val, GTSSumF tag val f, GTSSumF tag val g) => GTSTypeF tag val (f :+: g) where
    gtoTSTypeF lts = TSTypeF_ $
        TSGeneric ":+:" SNotObj (K "T" :* Nil) $ \rs (TSType_ t :* Nil) ->
          tsTaggedUnion tvo $ decide (\case L1 x -> Left x; R1 y -> Right y)
            (gtsSumF @tag @val @f (hmap (mapTSType_ (tsShift rs)) as) L1 t)
            (gtsSumF @tag @val @g (hmap (mapTSType_ (tsShift rs)) bs) R1 t)
      where
        tvo = def
          { tvoTagKey      = knownSymbolText @tag
          , tvoContentsKey = knownSymbolText @val
          }
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), KnownSymbol k, GTSTypeF tag val f, GTSObjectF tag val g)
      => GTSTypeF tag val ((M1 S ('MetaSel ('Just k) a b c) f) :*: g) where
    gtoTSTypeF lts = TSTypeF_ $
        TSGeneric ":*:" SIsObj (K "T" :* Nil) $ \rs (TSType_ t :* Nil) ->
          tsObject $
            (:*:) <$> gtsObjectF @tag @val @(M1 S ('MetaSel ('Just k) a b c) f)
                        (hmap (mapTSType_ (tsShift rs)) as)
                        (\(x :*: _) -> x)
                        t
                  <*> gtsObjectF @tag @val @g
                        (hmap (mapTSType_ (tsShift rs)) bs)
                        (\(_ :*: y) -> y)
                        t
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), GTSTypeF tag val f, GTSTupleF tag val g)
      => GTSTypeF tag val ((M1 S ('MetaSel 'Nothing a b c) f) :*: g) where
    gtoTSTypeF lts = TSTypeF_ $
        TSGeneric ":*:" SNotObj (K "T" :* Nil) $ \rs (TSType_ t :* Nil) ->
          tsTuple $
            (:*:) <$> gtsTupleF @tag @val @(M1 S ('MetaSel 'Nothing a b c) f)
                        (hmap (mapTSType_ (tsShift rs)) as)
                        (\(x :*: _) -> x)
                        t
                  <*> gtsTupleF @tag @val @g
                        (hmap (mapTSType_ (tsShift rs)) bs)
                        (\(_ :*: y) -> y)
                        t
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (KnownSymbol nm, GTSTypeF tag val f) => GTSTypeF tag val (M1 D ('MetaData nm a b c) f) where
    gtoTSTypeF lts = mapTSTypeF_
      (\tsg -> invmap M1 unM1 $ tsg { tsgName = knownSymbolText @nm })
      (gtoTSTypeF @tag @val @f lts)

instance GTSTypeF tag val f => GTSTypeF tag val (M1 S ('MetaSel s a b c) f) where
    gtoTSTypeF lts = mapTSTypeF_ (invmap M1 unM1) (gtoTSTypeF @tag @val @f lts)

instance GTSTypeF tag val f => GTSTypeF tag val (M1 C ('MetaCons constr a b) f) where
    gtoTSTypeF lts = mapTSTypeF_ (invmap M1 unM1) (gtoTSTypeF @tag @val @f lts)

instance GTSTypeF tag val Par1 where
    gtoTSTypeF _ = TSTypeF_ $
      TSGeneric "Par1" SNotObj (K "T" :* Nil) $ \_ (x :* Nil) ->
        onTSType_ id TSSingle (invmap Par1 unPar1 x)

instance GTSTypeF tag val (K1 i x) where
    gtoTSTypeF :: forall p n a. NP (TSType_ p n) '[x] -> TSTypeF_ p n '[a] (K1 i x a)
    gtoTSTypeF (TSType_ t :* Nil) = TSTypeF_ $
        TSGeneric "K1" (tsObjType t) (K "T" :* Nil) $ \rs _ ->
          tsShift @_ @p rs $ invmap K1 unK1 t

instance GTSTypeF tag val U1 where
    gtoTSTypeF _ = TSTypeF_ $
      TSGeneric "U1" SNotObj (K "T" :* Nil) $ \_ _ ->
        invmap (const U1) (const ()) $ TSPrimType (inject TSVoid)

instance GTSTypeF tag val V1 where
    gtoTSTypeF _ = TSTypeF_ $
      TSGeneric "V1" SNotObj (K "T" :* Nil) $ \_ _ ->
        invmap absurd (\case {}) $ TSPrimType (inject TSNever)


class GTSSumF (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsSumF
        :: NP (TSType_ p n) (LeafTypes f)
        -> (f a -> b)
        -> TSType p k n a
        -> TaggedBranches p n b (f a)

instance (All Top (LeafTypes f), GTSSumF tag val f, GTSSumF tag val g) => GTSSumF tag val (f :+: g) where
    gtsSumF lts f t = decide (\case L1 x -> Left x; R1 y -> Right y)
        (gtsSumF @tag @val @f as (f . L1) t)
        (gtsSumF @tag @val @g bs (f . R1) t)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance {-# OVERLAPS #-} (KnownSymbol constr, NotEqSym tag constr)
      => GTSSumF tag val (M1 C ('MetaCons constr a b) U1) where
    gtsSumF _ f _ = () >$ emptyTaggedBranch (f (M1 U1)) (knownSymbolText @constr)

-- | Will "flatten out" objects if possible
instance (KnownSymbol constr, NotEqSym tag constr, GTSTypeF tag val f)
      => GTSSumF tag val (M1 C ('MetaCons constr a b) f) where
    gtsSumF lts f t = withTSTypeF_
      (\tsg -> contramap unM1
             . taggedBranch (f . M1) (knownSymbolText @constr)
             . TSType_
             $ tsApply tsg (TSType_ t :* Nil)
      )
      (gtoTSTypeF @tag @val @f lts)

class GTSObjectF (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsObjectF
        :: NP (TSType_ p n) (LeafTypes f)
        -> (b -> f a)
        -> TSType p k n a
        -> ObjectProps p n b (f a)

instance (All Top (LeafTypes f), GTSObjectF tag val f, GTSObjectF tag val g) => GTSObjectF tag val (f :*: g) where
    gtsObjectF lts f t =
        (:*:) <$> gtsObjectF @tag @val @f as ((\(x :*: _) -> x) . f) t
              <*> gtsObjectF @tag @val @g bs ((\(_ :*: y) -> y) . f) t
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (KnownSymbol k, GTSTypeF tag val f) => GTSObjectF tag val (M1 S ('MetaSel ('Just k) a b c) f) where
    gtsObjectF lts f t = withTSTypeF_
      (\tsg -> M1 <$> keyVal True (unM1 . f) (knownSymbolText @k)
                        (TSType_ (tsApply tsg (TSType_ t :* Nil)))
      )
      (gtoTSTypeF @tag @val @f lts)

class GTSTupleF (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsTupleF :: NP (TSType_ p n) (LeafTypes f)
              -> (b -> f a)
              -> TSType p k n a
              -> TupleVals p n b (f a)

instance (All Top (LeafTypes f), GTSTupleF tag val f, GTSTupleF tag val g) => GTSTupleF tag val (f :*: g) where
    gtsTupleF lts f t =
        (:*:) <$> gtsTupleF @tag @val @f as ((\(x :*: _) -> x) . f) t
              <*> gtsTupleF @tag @val @g bs ((\(_ :*: y) -> y) . f) t
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance GTSTypeF tag val f => GTSTupleF tag val (M1 S ('MetaSel 'Nothing a b c) f) where
    gtsTupleF lts f t = withTSTypeF_
      (\tsg -> M1 <$> tupleVal (unM1 . f)
                        (TSType_ (tsApply tsg (TSType_ t :* Nil)))
      )
      (gtoTSTypeF @tag @val @f lts)

knownSymbolText :: forall s. KnownSymbol s => Text
knownSymbolText = T.pack (symbolVal (Proxy @s))
