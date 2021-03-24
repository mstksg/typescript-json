{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Typescript.Json.Types.SNat (
    Length
  , SNat_(..)
  , plusNat
  , vecToSNat_
  , prodVec
  , shiftFin
  , weakenFin
  , assocPlus
  , commutePlus
  , rightSuccPlus
  , zeroPlus
  , vecSame
  ) where

import           Data.Fin           (Fin(..))
import           Data.Kind
import           Data.SOP           (NP(..), K(..))
import           Data.Type.Equality
import           Data.Type.Nat
import           Data.Vec.Lazy      (Vec(..))

data SNat_ :: Nat -> Type where
    SZ_ :: SNat_ 'Z
    SS_ :: SNat_ n -> SNat_ ('S n)

type family Length (as :: [k]) :: Nat where
    Length '[] = 'Z
    Length (a ': as) = 'S (Length as)

plusNat
    :: SNat_ as
    -> SNat_ bs
    -> SNat_ (Plus as bs)
plusNat = \case
    SZ_ -> id
    SS_ n -> SS_ . plusNat n

vecToSNat_ :: forall n b. Vec n b -> SNat_ n
vecToSNat_ = \case
    VNil     -> SZ_
    _ ::: xs -> SS_ (vecToSNat_ xs)

prodVec :: NP (K a) as -> Vec (Length as) a
prodVec = \case
    Nil -> VNil
    K x :* xs -> x ::: prodVec xs

shiftFin
    :: forall as bs. ()
    => SNat_ as
    -> Fin bs
    -> Fin (Plus as bs)
shiftFin = \case
    SZ_ -> id
    SS_ n -> FS . shiftFin n

weakenFin
    :: forall as bs. ()
    => Fin as
    -> Fin (Plus as bs)
weakenFin = \case
    FZ   -> FZ
    FS i -> FS (weakenFin @_ @bs i)

assocPlus
    :: forall a b c. ()
    => SNat_ a
    -> Plus a (Plus b c) :~: Plus (Plus a b) c
assocPlus = \case
    SZ_ -> Refl
    SS_ n -> case assocPlus @_ @b @c n  of
      Refl -> Refl

commutePlus
    :: forall a b. ()
    => SNat_ a
    -> SNat_ b
    -> Plus a b :~: Plus b a
commutePlus = \case
    SZ_ -> \m -> case zeroPlus m of Refl -> Refl
    SS_ n -> \m -> case commutePlus n m of
      Refl -> case rightSuccPlus m n of
        Refl -> Refl

rightSuccPlus :: SNat_ a -> SNat_ b -> 'S (Plus a b) :~: Plus a ('S b)
rightSuccPlus = \case
    SZ_ -> \_ -> Refl
    SS_ n -> \m -> case rightSuccPlus n m of Refl -> Refl

zeroPlus :: SNat_ a -> a :~: Plus a 'Z
zeroPlus = \case
    SZ_ -> Refl
    SS_ n -> case zeroPlus n of Refl -> Refl

vecSame :: Vec n a -> Vec m a -> Maybe (n :~: m)
vecSame = \case
  VNil -> \case
    VNil -> Just Refl
    _    -> Nothing
  _ ::: xs -> \case
    VNil -> Nothing
    _ ::: ys -> (\case Refl -> Refl) <$> vecSame xs ys

