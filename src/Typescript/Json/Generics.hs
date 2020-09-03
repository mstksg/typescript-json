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
  -- * Combinators
    mergeUnion
  , mergeObjProd
  , mergeTupProd
  , emptyConstr
  , singleConstr
  , singleMember
  -- * Typeclass-based
  , GTSType(..)
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
import           Data.Functor.Combinator
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divisible.Free (Dec(..))
import           Data.Functor.Invariant
import           Data.HFunctor
import           Data.HFunctor.Route
import           Data.Kind
import           Data.Proxy
import           Data.SOP                                  (NP(..), NS(..), I(..), K(..), (:.:)(..), hpure, All, Top)
import           Data.Scientific
import           Data.Text                                 (Text)
import           Data.Type.Nat                             (Plus)
import           Data.Void
import           GHC.Generics
import           GHC.TypeLits
import           Typescript.Json.Core
import           Typescript.Json.Core.Combinators
import qualified Control.Applicative.Lift                  as Lift
import qualified Data.SOP                                  as SOP
import qualified Data.Text                                 as T
import qualified Data.Type.Nat                             as Nat

type family WarnIfEq (b :: Ordering) (c :: ErrorMessage) :: Constraint where
    WarnIfEq 'LT c = ()
    WarnIfEq 'EQ c = TypeError c
    WarnIfEq 'GT c = ()

type NotEqSym a b = WarnIfEq (CmpSymbol a b)
                ('Text "Cannot derive instance: constructor and tag value are both "
           ':<>: 'Text a
                )

class ToTSType a where
    toTSType :: TSType_ ps n a

    default toTSType :: (Generic a, GTSType "tag" "contents" (Rep a), All ToTSType (LeafTypes (Rep a))) => TSType_ ps n a
    toTSType = genericToTSType_ @"tag" @"contents" @a

instance ToTSType Int where
    toTSType = TSType_ . TSPrimType $
      PS TSNumber
        (\x -> case toBoundedInteger x of
            Nothing -> Left . T.pack $ "Not an integer: " <> show x
            Just i  -> Right i
        )
        fromIntegral

instance ToTSType Double where
    toTSType = TSType_ . TSPrimType
             . invmap realToFrac realToFrac
             $ inject TSNumber

instance ToTSType Bool where
    toTSType = TSType_ . TSPrimType $ inject TSBoolean

instance ToTSType Text where
    toTSType = TSType_ . TSPrimType $ inject TSString

instance ToTSType a => ToTSType [a] where
    toTSType = case toTSType @a of
      TSType_ t -> TSType_ $ TSArray (ilan t)

instance ToTSType a => ToTSType (Maybe a) where
    toTSType = genericToTSType1_ @"tag" @"contents" toTSType

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
    '[] ++ bs = bs
    (a ': as) ++ bs = a ': (as ++ bs)

genericToTSType_
    :: forall tag val a ps n.
     ( Generic a, GTSType tag val (Rep a), All ToTSType (LeafTypes (Rep a)) )
    => TSType_ ps n a
genericToTSType_ = genericToTSType @tag @val @a (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSType
    :: forall tag val a ps n. (Generic a, GTSType tag val (Rep a))
    => NP (TSType_ ps n) (LeafTypes (Rep a))
    -> TSType_ ps n a
genericToTSType = invmap to from . gtoTSType @tag @val @(Rep a)

genericToTSType1_
    :: forall tag val f ps n a. (Generic1 f, GTSTypeF tag val (Rep1 f), All ToTSType (LeafTypes (Rep1 f)))
    => TSType_ ps n a
    -> TSType_ ps n (f a)
genericToTSType1_ = genericToTSType1 @tag @val @f (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSType1
    :: forall tag val f ps n a. (Generic1 f, GTSTypeF tag val (Rep1 f))
    => NP (TSType_ ps n) (LeafTypes (Rep1 f))
    -> TSType_ ps n a
    -> TSType_ ps n (f a)
genericToTSType1 lts tx = case genericToTSTypeF @tag @val @f lts of
    TSTypeF_ tf -> TSType_ $ TSApply tf (tx :* Nil)

genericToTSTypeF_
    :: forall tag val f ps n a. (Generic1 f, GTSTypeF tag val (Rep1 f), All ToTSType (LeafTypes (Rep1 f)))
    => TSTypeF_ ps n '[a] (f a)
genericToTSTypeF_ = genericToTSTypeF @tag @val @f (SOP.hcpure (Proxy @ToTSType) toTSType)

genericToTSTypeF
    :: forall tag val f ps n a. (Generic1 f, GTSTypeF tag val (Rep1 f))
    => NP (TSType_ ps n) (LeafTypes (Rep1 f))
    -> TSTypeF_ ps n '[a] (f a)
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
    gtoTSType :: NP (TSType_ ps n) (LeafTypes f) -> TSType_ ps n (f x)

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

instance (All Top (LeafTypes f), GTSSum tag val f, GTSSum tag val g) => GTSType tag val (f :+: g) where
    gtoTSType lts = TSType_ . TSUnion $
        mergeUnion (gtsSum @tag @val @f as) (gtsSum @tag @val @g bs)
      where
        (as, bs) = splitNP (hpure Proxy) lts

mergeUnion
    :: PostT Dec (TSType_ ps n) (f x)
    -> PostT Dec (TSType_ ps n) (g x)
    -> PostT Dec (TSType_ ps n) ((f :+: g) x)
mergeUnion (PostT oX) (PostT oY) = PostT $
        decide (\case L1 x -> Left x; R1 y -> Right y)
          (hmap (mapPost L1) oX)
          (hmap (mapPost R1) oY)

instance (All Top (LeafTypes f), KnownSymbol k, GTSType tag val f, GTSObject tag val g)
      => GTSType tag val ((M1 S ('MetaSel ('Just k) a b c) f) :*: g) where
    gtoTSType lts = TSType_ . TSObject $
        mergeObjProd
          (gtsObject @tag @val @(M1 S ('MetaSel ('Just k) a b c) f) as)
          (gtsObject @tag @val @g bs)
      where
        (as, bs) = splitNP (hpure Proxy) lts

mergeObjProd
    :: TSKeyVal ps n (f x)
    -> TSKeyVal ps n (g x)
    -> TSKeyVal ps n ((f :*: g) x)
mergeObjProd (PreT oX) (PreT oY) = PreT $
    (:*:) <$> hmap (mapPre (\(x :*: _) -> x)) oX
          <*> hmap (mapPre (\(_ :*: y) -> y)) oY

instance (All Top (LeafTypes f), GTSType tag val f, GTSTuple tag val g)
      => GTSType tag val ((M1 S ('MetaSel 'Nothing a b c) f) :*: g) where
    gtoTSType lts = TSType_ . TSTuple $
        mergeTupProd
          (gtsTuple @tag @val @(M1 S ('MetaSel 'Nothing a b c) f) as)
          (gtsTuple @tag @val @g bs)
      where
        (as, bs) = splitNP (hpure Proxy) lts

mergeTupProd
    :: PreT Ap (TSType_ ps n) (f x)
    -> PreT Ap (TSType_ ps n) (g x)
    -> PreT Ap (TSType_ ps n) ((f :*: g) x)
mergeTupProd (PreT oX) (PreT oY) = PreT $
    (:*:) <$> hmap (mapPre (\(x :*: _) -> x)) oX
          <*> hmap (mapPre (\(_ :*: y) -> y)) oY

class GTSSum (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsSum
        :: NP (TSType_ ps n) (LeafTypes f)
        -> PostT Dec (TSType_ ps n) (f x)

instance (All Top (LeafTypes f), GTSSum tag val f, GTSSum tag val g) => GTSSum tag val (f :+: g) where
    gtsSum lts = mergeUnion (gtsSum @tag @val @f as) (gtsSum @tag @val @g bs)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance {-# OVERLAPS #-} (KnownSymbol tag, KnownSymbol constr, NotEqSym tag constr)
      => GTSSum tag conts (M1 C ('MetaCons constr a b) U1) where
    gtsSum _ = emptyConstr (knownSymbolText @tag) (knownSymbolText @constr)

emptyConstr
    :: Monoid m
    => Text
    -> Text
    -> PostT Dec (TSType_ ps n) m
emptyConstr tag constr = invmap mempty mempty . PostT $
    injectPost id $ TSType_ . TSObject . PreT $
      injectPre (const ()) $ ObjMember
        { objMemberKey = tag
        , objMemberVal = L1 . TSType_ . TSPrimType $
            inject (TSStringLit constr)
        }

-- | Will "flatten out" objects if possible
instance (KnownSymbol tag, KnownSymbol val, KnownSymbol constr, NotEqSym tag constr, GTSType tag val f)
      => GTSSum tag val (M1 C ('MetaCons constr a b) f) where
    gtsSum lts = singleConstr (knownSymbolText @tag) (knownSymbolText @val) (knownSymbolText @constr)
               . invmap M1 unM1
               $ gtoTSType @tag @val @f lts

singleConstr
    :: Inject t
    => Text
    -> Text
    -> Text
    -> TSType_ ps n (f p)
    -> PostT t (TSType_ ps n) (f p)
singleConstr tag val constr px = PostT $
    injectPost id $ onTSType_
      (\x -> TSType_ . TSObject . PreT $
             tagObj
          *> injectPre id ObjMember
               { objMemberKey = val
               , objMemberVal = L1 (TSType_ x)
               }
      )
      (\x -> TSType_ . TSIntersection . PreT $
             injectPre (const ()) (TSObject (PreT tagObj))
          *> injectPre id         x
      )
      px
  where
    tagObj :: forall x ps n. Ap (Pre x (ObjMember (TSType_ ps n))) ()
    tagObj = injectPre (const ()) $ ObjMember
        { objMemberKey = tag
        , objMemberVal = L1 . TSType_ . TSPrimType $
            inject (TSStringLit constr)
        }

class GTSObject (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsObject :: NP (TSType_ ps n) (LeafTypes f) -> TSKeyVal ps n (f x)

instance (All Top (LeafTypes f), GTSObject tag val f, GTSObject tag val g) => GTSObject tag val (f :*: g) where
    gtsObject lts = mergeObjProd
        (gtsObject @tag @val @f as)
        (gtsObject @tag @val @g bs)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (KnownSymbol k, GTSType tag val f) => GTSObject tag val (M1 S ('MetaSel ('Just k) a b c) f) where
    gtsObject lts = invmap M1 unM1
                  $ singleMember (knownSymbolText @k) (gtoTSType @tag @val @f lts)

singleMember
    :: Text
    -> TSType_ ps n a
    -> TSKeyVal ps n a
singleMember k t = PreT $
    injectPre id $ ObjMember
      { objMemberKey = k
      , objMemberVal = L1 t
      }


class GTSTuple (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsTuple :: NP (TSType_ ps n) (LeafTypes f) -> PreT Ap (TSType_ ps n) (f x)

instance (All Top (LeafTypes f), GTSTuple tag val f, GTSTuple tag val g) => GTSTuple tag val (f :*: g) where
    gtsTuple lts = mergeTupProd
        (gtsTuple @tag @val @f as)
        (gtsTuple @tag @val @g bs)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance GTSType tag val f => GTSTuple tag val (M1 S ('MetaSel 'Nothing a b c) f) where
    gtsTuple lts = PreT $
      injectPre id $
        invmap M1 unM1 (gtoTSType @tag @val @f lts)





class GTSTypeF (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtoTSTypeF :: NP (TSType_ ps n) (LeafTypes f) -> TSTypeF_ ps n '[a] (f a)

instance (All Top (LeafTypes f), GTSSumF tag val f, GTSSumF tag val g) => GTSTypeF tag val (f :+: g) where
    gtoTSTypeF lts = TSTypeF_ $
        TSGeneric ":+:" SNotObj (K "T" :* Nil) $ \rs (TSType_ t :* Nil) ->
          TSUnion $ mergeUnion
            (gtsSumF @tag @val @f (hmap (mapTSType_ (tsShift rs)) as) t)
            (gtsSumF @tag @val @g (hmap (mapTSType_ (tsShift rs)) bs) t)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), KnownSymbol k, GTSTypeF tag val f, GTSObjectF tag val g)
      => GTSTypeF tag val ((M1 S ('MetaSel ('Just k) a b c) f) :*: g) where
    gtoTSTypeF lts = TSTypeF_ $
        TSGeneric ":*:" SIsObj (K "T" :* Nil) $ \rs (TSType_ t :* Nil) ->
          TSObject $ mergeObjProd
            (gtsObjectF @tag @val @(M1 S ('MetaSel ('Just k) a b c) f)
                (hmap (mapTSType_ (tsShift rs)) as) t
            )
            (gtsObjectF @tag @val @g (hmap (mapTSType_ (tsShift rs)) bs) t)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (All Top (LeafTypes f), GTSTypeF tag val f, GTSTupleF tag val g)
      => GTSTypeF tag val ((M1 S ('MetaSel 'Nothing a b c) f) :*: g) where
    gtoTSTypeF lts = TSTypeF_ $
        TSGeneric ":*:" SNotObj (K "T" :* Nil) $ \rs (TSType_ t :* Nil) ->
          TSTuple $ mergeTupProd
            (gtsTupleF @tag @val @(M1 S ('MetaSel 'Nothing a b c) f)
                (hmap (mapTSType_ (tsShift rs)) as) t
            )
            (gtsTupleF @tag @val @g (hmap (mapTSType_ (tsShift rs)) bs) t)
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
    gtoTSTypeF :: forall ps n a. NP (TSType_ ps n) '[x] -> TSTypeF_ ps n '[a] (K1 i x a)
    gtoTSTypeF (TSType_ t :* Nil) = TSTypeF_ $
        TSGeneric "K1" (tsObjType t) (K "T" :* Nil) $ \rs _ ->
          tsShift @_ @ps rs $ invmap K1 unK1 t

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
        :: NP (TSType_ ps n) (LeafTypes f)
        -> TSType ps ks n a
        -> PostT Dec (TSType_ ps n) (f a)

instance (All Top (LeafTypes f), GTSSumF tag val f, GTSSumF tag val g) => GTSSumF tag val (f :+: g) where
    gtsSumF lts t = mergeUnion
        (gtsSumF @tag @val @f as t)
        (gtsSumF @tag @val @g bs t)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance {-# OVERLAPS #-} (KnownSymbol tag, KnownSymbol constr, NotEqSym tag constr)
      => GTSSumF tag val (M1 C ('MetaCons constr a b) U1) where
    gtsSumF _ _ = emptyConstr (knownSymbolText @tag) (knownSymbolText @constr)

-- | Will "flatten out" objects if possible
instance (KnownSymbol tag, KnownSymbol val, KnownSymbol constr, NotEqSym tag constr, GTSTypeF tag val f)
      => GTSSumF tag val (M1 C ('MetaCons constr a b) f) where
    gtsSumF lts t = case gtoTSTypeF @tag @val @f lts of
      TSTypeF_ tsg -> invmap M1 unM1
                    . singleConstr (knownSymbolText @tag) (knownSymbolText @val) (knownSymbolText @constr)
                    . TSType_
                    $ tsApply tsg (TSType_ t :* Nil)

class GTSObjectF (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsObjectF
        :: NP (TSType_ ps n) (LeafTypes f)
        -> TSType ps ks n a
        -> TSKeyVal ps n (f a)

instance (All Top (LeafTypes f), GTSObjectF tag val f, GTSObjectF tag val g) => GTSObjectF tag val (f :*: g) where
    gtsObjectF lts t = mergeObjProd
        (gtsObjectF @tag @val @f as t)
        (gtsObjectF @tag @val @g bs t)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance (KnownSymbol k, GTSTypeF tag val f) => GTSObjectF tag val (M1 S ('MetaSel ('Just k) a b c) f) where
    gtsObjectF lts t = case gtoTSTypeF @tag @val @f lts of
      TSTypeF_ tsg -> invmap M1 unM1
                    . singleMember (knownSymbolText @k)
                    . TSType_
                    $ tsApply tsg (TSType_ t :* Nil)

class GTSTupleF (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsTupleF :: NP (TSType_ ps n) (LeafTypes f)
              -> TSType ps ks n a
              -> PreT Ap (TSType_ ps n) (f a)

instance (All Top (LeafTypes f), GTSTupleF tag val f, GTSTupleF tag val g) => GTSTupleF tag val (f :*: g) where
    gtsTupleF lts t = mergeTupProd
        (gtsTupleF @tag @val @f as t)
        (gtsTupleF @tag @val @g bs t)
      where
        (as, bs) = splitNP (hpure Proxy) lts

instance GTSTypeF tag val f => GTSTupleF tag val (M1 S ('MetaSel 'Nothing a b c) f) where
    gtsTupleF lts t = case gtoTSTypeF @tag @val @f lts of
      TSTypeF_ tsg -> PreT $ injectPre id $
        invmap M1 unM1 (TSType_ (tsApply tsg (TSType_ t :* Nil)))

knownSymbolText :: forall s. KnownSymbol s => Text
knownSymbolText = T.pack (symbolVal (Proxy @s))
