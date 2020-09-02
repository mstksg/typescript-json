{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Typescript.Json.Generics (
    ToTSType(..)
  , GTSType(..)
  , GTSSum(..)
  , GTSObject(..)
  , GTSTuple(..)
  , GTSTypeF(..)
  , GTSSumF(..)
  , GTSObjectF(..)
  , GTSTupleF(..)
  ) where

import           Data.Functor.Combinator
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divisible.Free (Dec(..))
import           Data.Functor.Invariant
import           Data.HFunctor
import           Data.HFunctor.Route
import           Data.Kind
import           Data.Proxy
import           Data.SOP                                  (NP(..), NS(..), I(..), K(..), (:.:)(..))
import           Data.Scientific
import           Data.Text                                 (Text)
import           Data.Type.Nat                             (Plus)
import           Data.Void
import           GHC.Generics
import           GHC.TypeLits
import           Typescript.Json.Core
import           Typescript.Json.Core.Combinators
import qualified Control.Applicative.Lift                  as Lift
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

class GTSType (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtoTSType :: TSType_ ps n (f x)

instance (KnownSymbol nm, GTSType tag val f) => GTSType tag val (M1 D ('MetaData nm a b c) f) where
    gtoTSType = mapTSType_
      (TSNamed (knownSymbolText @nm) . invmap M1 unM1)
      (gtoTSType @tag @val @f)

instance GTSType tag val f => GTSType tag val (M1 S ('MetaSel s a b c) f) where
    gtoTSType = mapTSType_ (invmap M1 unM1) (gtoTSType @tag @val @f)

instance GTSType tag val f => GTSType tag val (M1 C ('MetaCons constr a b) f) where
    gtoTSType = mapTSType_ (invmap M1 unM1) (gtoTSType @tag @val @f)

instance ToTSType a => GTSType tag val (K1 i a) where
    gtoTSType = invmap K1 unK1 (toTSType @a)

instance GTSType tag val U1 where
    gtoTSType = TSType_ . invmap (const U1) (const ()) $ TSPrimType (inject TSVoid)

instance GTSType tag val V1 where
    gtoTSType = TSType_ . invmap absurd (\case {}) $ TSPrimType (inject TSNever)

instance (GTSSum tag val f, GTSSum tag val g) => GTSType tag val (f :+: g) where
    gtoTSType = TSType_ . TSUnion $
      mergeUnion (gtsSum @tag @val @f) (gtsSum @tag @val @g)

mergeUnion
    :: PostT Dec (TSType_ ps n) (f x)
    -> PostT Dec (TSType_ ps n) (g x)
    -> PostT Dec (TSType_ ps n) ((f :+: g) x)
mergeUnion (PostT oX) (PostT oY) = PostT $
        decide (\case L1 x -> Left x; R1 y -> Right y)
          (hmap (mapPost L1) oX)
          (hmap (mapPost R1) oY)

instance (KnownSymbol k, GTSType tag val f, GTSObject tag val g)
      => GTSType tag val ((M1 S ('MetaSel ('Just k) a b c) f) :*: g) where
    gtoTSType = TSType_ . TSObject $
      mergeObjProd
        (gtsObject @tag @val @(M1 S ('MetaSel ('Just k) a b c) f))
        (gtsObject @tag @val @g)

mergeObjProd
    :: TSKeyVal ps n (f x)
    -> TSKeyVal ps n (g x)
    -> TSKeyVal ps n ((f :*: g) x)
mergeObjProd (PreT oX) (PreT oY) = PreT $
    (:*:) <$> hmap (mapPre (\(x :*: _) -> x)) oX
          <*> hmap (mapPre (\(_ :*: y) -> y)) oY


instance (GTSType tag val f, GTSTuple tag val g)
      => GTSType tag val ((M1 S ('MetaSel 'Nothing a b c) f) :*: g) where
    gtoTSType = TSType_ . TSTuple $
      mergeTupProd
        (gtsTuple @tag @val @(M1 S ('MetaSel 'Nothing a b c) f))
        (gtsTuple @tag @val @g)

mergeTupProd
    :: PreT Ap (TSType_ ps n) (f x)
    -> PreT Ap (TSType_ ps n) (g x)
    -> PreT Ap (TSType_ ps n) ((f :*: g) x)
mergeTupProd (PreT oX) (PreT oY) = PreT $
    (:*:) <$> hmap (mapPre (\(x :*: _) -> x)) oX
          <*> hmap (mapPre (\(_ :*: y) -> y)) oY

class GTSSum (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsSum :: PostT Dec (TSType_ ps n) (f x)

instance (GTSSum tag val f, GTSSum tag val g) => GTSSum tag val (f :+: g) where
    gtsSum = mergeUnion (gtsSum @tag @val @f) (gtsSum @tag @val @g)

instance {-# OVERLAPS #-} (KnownSymbol tag, KnownSymbol constr, NotEqSym tag constr)
      => GTSSum tag conts (M1 C ('MetaCons constr a b) U1) where
    gtsSum = emptyConstr (knownSymbolText @tag) (knownSymbolText @constr)

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
      => GTSSum tag conts (M1 C ('MetaCons constr a b) f) where
    gtsSum = singleConstr (knownSymbolText @tag) (knownSymbolText @val) (knownSymbolText @constr)
           . invmap M1 unM1
           $ gtoTSType @tag @val @f

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
    gtsObject :: TSKeyVal ps n (f x)

instance (GTSObject tag val f, GTSObject tag val g) => GTSObject tag val (f :*: g) where
    gtsObject = mergeObjProd (gtsObject @tag @val @f) (gtsObject @tag @val @g)

instance (KnownSymbol k, GTSType tag val f) => GTSObject tag val (M1 S ('MetaSel ('Just k) a b c) f) where
    gtsObject = invmap M1 unM1
              $ singleMember (knownSymbolText @k) (gtoTSType @tag @val @f)

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
    gtsTuple :: PreT Ap (TSType_ ps n) (f x)

instance (GTSTuple tag val f, GTSTuple tag val g) => GTSTuple tag val (f :*: g) where
    gtsTuple = mergeTupProd (gtsTuple @tag @val @f) (gtsTuple @tag @val @g)

instance GTSType tag val f => GTSTuple tag val (M1 S ('MetaSel 'Nothing a b c) f) where
    gtsTuple = PreT $
      injectPre id $
        invmap M1 unM1 (gtoTSType @tag @val @f)





class GTSTypeF (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtoTSTypeF :: TSTypeF_ ps n '[a] (f a)

instance (GTSSumF tag val f, GTSSumF tag val g) => GTSTypeF tag val (f :+: g) where
    gtoTSTypeF = TSTypeF_ $
      TSGeneric ":+:" SNotObj (K "T" :* Nil) $ \_ (TSType_ t :* Nil) ->
        TSUnion $
          mergeUnion (gtsSumF @tag @val @f t) (gtsSumF @tag @val @g t)

instance (KnownSymbol k, GTSTypeF tag val f, GTSObjectF tag val g)
      => GTSTypeF tag val ((M1 S ('MetaSel ('Just k) a b c) f) :*: g) where
    gtoTSTypeF = TSTypeF_ $
      TSGeneric ":*:" SIsObj (K "T" :* Nil) $ \_ (TSType_ t :* Nil) ->
        TSObject $ mergeObjProd
          (gtsObjectF @tag @val @(M1 S ('MetaSel ('Just k) a b c) f) t)
          (gtsObjectF @tag @val @g t)

instance (GTSTypeF tag val f, GTSTupleF tag val g)
      => GTSTypeF tag val ((M1 S ('MetaSel 'Nothing a b c) f) :*: g) where
    gtoTSTypeF = TSTypeF_ $
      TSGeneric ":*:" SNotObj (K "T" :* Nil) $ \_ (TSType_ t :* Nil) ->
        TSTuple $ mergeTupProd
          (gtsTupleF @tag @val @(M1 S ('MetaSel 'Nothing a b c) f) t)
          (gtsTupleF @tag @val @g t)

instance (KnownSymbol nm, GTSTypeF tag val f) => GTSTypeF tag val (M1 D ('MetaData nm a b c) f) where
    gtoTSTypeF :: forall ps n x. TSTypeF_ ps n '[x] (M1 D ('MetaData nm a b c) f x)
    gtoTSTypeF = mapTSTypeF_
      (\tsg -> invmap M1 unM1 $ tsg { tsgName = knownSymbolText @nm })
      (gtoTSTypeF @tag @val @f)

instance GTSTypeF tag val f => GTSTypeF tag val (M1 S ('MetaSel s a b c) f) where
    gtoTSTypeF = mapTSTypeF_ (invmap M1 unM1) (gtoTSTypeF @tag @val @f)

instance GTSTypeF tag val f => GTSTypeF tag val (M1 C ('MetaCons constr a b) f) where
    gtoTSTypeF = mapTSTypeF_ (invmap M1 unM1) (gtoTSTypeF @tag @val @f)

instance GTSTypeF tag val Par1 where
    gtoTSTypeF :: forall ps n a. TSTypeF_ ps n '[a] (Par1 a)
    gtoTSTypeF = TSTypeF_ $
      TSGeneric "Par1" SNotObj (K "T" :* Nil) $ \_ (x :* Nil) ->
        onTSType_ id TSSingle (invmap Par1 unPar1 x)

instance ToTSType x => GTSTypeF tag val (K1 i x) where
    gtoTSTypeF :: forall ps n a. TSTypeF_ ps n '[a] (K1 i x a)
    gtoTSTypeF = case toTSType @x of
      TSType_ t -> TSTypeF_ $
        TSGeneric "K1" (tsObjType t) (K "T" :* Nil) $ \rs _ ->
          tsShift @_ @ps rs $ invmap K1 unK1 t

instance GTSTypeF tag val U1 where
    gtoTSTypeF = TSTypeF_ $
      TSGeneric "U1" SNotObj (K "T" :* Nil) $ \_ _ ->
        invmap (const U1) (const ()) $ TSPrimType (inject TSVoid)

instance GTSTypeF tag val V1 where
    gtoTSTypeF = TSTypeF_ $
      TSGeneric "V1" SNotObj (K "T" :* Nil) $ \_ _ ->
        invmap absurd (\case {}) $ TSPrimType (inject TSNever)


class GTSSumF (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsSumF
        :: TSType ps ks n a
        -> PostT Dec (TSType_ ps n) (f a)

instance (GTSSumF tag val f, GTSSumF tag val g) => GTSSumF tag val (f :+: g) where
    gtsSumF t = mergeUnion
      (gtsSumF @tag @val @f t)
      (gtsSumF @tag @val @g t)

instance {-# OVERLAPS #-} (KnownSymbol tag, KnownSymbol constr, NotEqSym tag constr)
      => GTSSumF tag val (M1 C ('MetaCons constr a b) U1) where
    gtsSumF _ = emptyConstr (knownSymbolText @tag) (knownSymbolText @constr)

-- | Will "flatten out" objects if possible
instance (KnownSymbol tag, KnownSymbol val, KnownSymbol constr, NotEqSym tag constr, GTSTypeF tag val f)
      => GTSSumF tag val (M1 C ('MetaCons constr a b) f) where
    gtsSumF t = case gtoTSTypeF @tag @val @f of
      TSTypeF_ tsg -> invmap M1 unM1
                    . singleConstr (knownSymbolText @tag) (knownSymbolText @val) (knownSymbolText @constr)
                    . TSType_
                    $ tsApply tsg (TSType_ t :* Nil)

class GTSObjectF (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsObjectF
        :: TSType ps ks n a
        -> TSKeyVal ps n (f a)

instance (GTSObjectF tag val f, GTSObjectF tag val g) => GTSObjectF tag val (f :*: g) where
    gtsObjectF t = mergeObjProd (gtsObjectF @tag @val @f t) (gtsObjectF @tag @val @g t)

instance (KnownSymbol k, GTSTypeF tag val f) => GTSObjectF tag val (M1 S ('MetaSel ('Just k) a b c) f) where
    gtsObjectF t = case gtoTSTypeF @tag @val @f of
      TSTypeF_ tsg -> invmap M1 unM1
                    . singleMember (knownSymbolText @k)
                    . TSType_
                    $ tsApply tsg (TSType_ t :* Nil)

class GTSTupleF (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsTupleF :: TSType ps ks n a
              -> PreT Ap (TSType_ ps n) (f a)

instance (GTSTupleF tag val f, GTSTupleF tag val g) => GTSTupleF tag val (f :*: g) where
    gtsTupleF t = mergeTupProd (gtsTupleF @tag @val @f t) (gtsTupleF @tag @val @g t)

instance GTSTypeF tag val f => GTSTupleF tag val (M1 S ('MetaSel 'Nothing a b c) f) where
    gtsTupleF t = case gtoTSTypeF @tag @val @f of
      TSTypeF_ tsg -> PreT $ injectPre id $
        invmap M1 unM1 (TSType_ (tsApply tsg (TSType_ t :* Nil)))

knownSymbolText :: forall s. KnownSymbol s => Text
knownSymbolText = T.pack (symbolVal (Proxy @s))
