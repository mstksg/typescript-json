{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
  ) where

import           Data.Functor.Combinator
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divisible.Free (Dec(..))
import           Data.Functor.Invariant
import           Data.HFunctor
import           Data.HFunctor.Route
import           Data.Kind
import           Data.Proxy
import           Data.Scientific
import           Data.Text                                 (Text)
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

instance (GTSSum tag val f, GTSSum tag val g) => GTSType tag val (f :+: g) where
    gtoTSType = TSType_ . TSUnion $
      mergeUnion (gtsSum @tag @val @f) (gtsSum @tag @val @g)

instance (KnownSymbol k, GTSType tag val f, GTSObject tag val g)
      => GTSType tag val ((M1 S ('MetaSel ('Just k) a b c) f) :*: g) where
    gtoTSType = TSType_ . TSObject $
      mergeObjProd
        (gtsObject @tag @val @(M1 S ('MetaSel ('Just k) a b c) f))
        (gtsObject @tag @val @g)

instance (GTSType tag val f, GTSTuple tag val g)
      => GTSType tag val ((M1 S ('MetaSel 'Nothing a b c) f) :*: g) where
    gtoTSType = TSType_ . TSTuple $
      mergeTupProd
        (gtsTuple @tag @val @(M1 S ('MetaSel 'Nothing a b c) f))
        (gtsTuple @tag @val @g)

instance ToTSType a => GTSType tag val (K1 i a) where
    gtoTSType = invmap K1 unK1 (toTSType @a)

instance GTSType tag val U1 where
    gtoTSType = TSType_ . invmap (const U1) (const ()) $ TSPrimType (inject TSVoid)

class GTSSum (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsSum :: PostT Dec (TSType_ ps n) (f x)

instance (GTSSum tag val f, GTSSum tag val g) => GTSSum tag val (f :+: g) where
    gtsSum = PostT $
        decide (\case L1 x -> Left x; R1 y -> Right y)
          (hmap (mapPost L1) oX)
          (hmap (mapPost R1) oY)
      where
        PostT oX = gtsSum @tag @val @f
        PostT oY = gtsSum @tag @val @g

-- | Will "flatten out" objects if possible
instance {-# OVERLAPS #-} (KnownSymbol tag, KnownSymbol constr, NotEqSym tag constr)
      => GTSSum tag conts (M1 C ('MetaCons constr a b) U1) where
    gtsSum = PostT $
        injectPost id $ TSType_ . TSObject . invmap (const (M1 U1)) (const ()) . PreT $
          injectPre (const ()) $ ObjMember
            { objMemberKey = knownSymbolText @tag
            , objMemberVal = L1 . TSType_ . TSPrimType $
                inject (TSStringLit (knownSymbolText @constr))
            }


-- | Will "flatten out" objects if possible
instance (KnownSymbol tag, KnownSymbol conts, KnownSymbol constr, NotEqSym tag constr, GTSType tag val f)
      => GTSSum tag conts (M1 C ('MetaCons constr a b) f) where
    gtsSum = PostT $
        injectPost id $ onTSType_
          (\x -> TSType_ . TSObject . PreT $
                 tagObj
              *> injectPre id ObjMember
                   { objMemberKey = knownSymbolText @conts
                   , objMemberVal = L1 (TSType_ x)
                   }
          )
          (\x -> TSType_ . TSIntersection . PreT $
                 injectPre (const ()) (TSObject (PreT tagObj))
              *> injectPre id         x
          )
          (invmap M1 unM1 (gtoTSType @tag @val @f))
      where
        tagObj :: forall x ps n. Ap (Pre x (ObjMember (TSType_ ps n))) ()
        tagObj = injectPre (const ()) $ ObjMember
            { objMemberKey = knownSymbolText @tag
            , objMemberVal = L1 . TSType_ . TSPrimType $
                inject (TSStringLit (knownSymbolText @constr))
            }

mergeUnion
    :: PostT Dec (TSType_ ps n) (f x)
    -> PostT Dec (TSType_ ps n) (g x)
    -> PostT Dec (TSType_ ps n) ((f :+: g) x)
mergeUnion (PostT oX) (PostT oY) = PostT $
        decide (\case L1 x -> Left x; R1 y -> Right y)
          (hmap (mapPost L1) oX)
          (hmap (mapPost R1) oY)

class GTSObject (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsObject :: TSKeyVal ps n (f x)

instance (GTSObject tag val f, GTSObject tag val g) => GTSObject tag val (f :*: g) where
    gtsObject = mergeObjProd (gtsObject @tag @val @f) (gtsObject @tag @val @g)

mergeObjProd
    :: TSKeyVal ps n (f x)
    -> TSKeyVal ps n (g x)
    -> TSKeyVal ps n ((f :*: g) x)
mergeObjProd (PreT oX) (PreT oY) = PreT $
    (:*:) <$> hmap (mapPre (\(x :*: _) -> x)) oX
          <*> hmap (mapPre (\(_ :*: y) -> y)) oY

instance (KnownSymbol k, GTSType tag val f) => GTSObject tag val (M1 S ('MetaSel ('Just k) a b c) f) where
    gtsObject = PreT $
      injectPre id $ ObjMember
        { objMemberKey = knownSymbolText @k
        , objMemberVal = L1 . invmap M1 unM1 $ gtoTSType @tag @val @f
        }

class GTSTuple (tag :: Symbol) (val :: Symbol) (f :: Type -> Type) where
    gtsTuple :: PreT Ap (TSType_ ps n) (f x)

instance (GTSTuple tag val f, GTSTuple tag val g) => GTSTuple tag val (f :*: g) where
    gtsTuple = mergeTupProd (gtsTuple @tag @val @f) (gtsTuple @tag @val @g)

instance GTSType tag val f => GTSTuple tag val (M1 S ('MetaSel 'Nothing a b c) f) where
    gtsTuple = PreT $
      injectPre id $
        invmap M1 unM1 (gtoTSType @tag @val @f)

mergeTupProd
    :: PreT Ap (TSType_ ps n) (f x)
    -> PreT Ap (TSType_ ps n) (g x)
    -> PreT Ap (TSType_ ps n) ((f :*: g) x)
mergeTupProd (PreT oX) (PreT oY) = PreT $
    (:*:) <$> hmap (mapPre (\(x :*: _) -> x)) oX
          <*> hmap (mapPre (\(_ :*: y) -> y)) oY


knownSymbolText :: forall s. KnownSymbol s => Text
knownSymbolText = T.pack (symbolVal (Proxy @s))
