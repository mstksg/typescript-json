{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes                #-}

module Typescript.Json.Core.Combinators (
    PS(..)
  , ILan(..)
  , ilan
  , interpretILan
  , interpretCoILan
  , interpretContraILan
  ) where

import           Data.Functor.Combinator
import           Data.Functor.Invariant
import           Data.Functor.Contravariant
import           Data.Text (Text)

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

data ILan g h a = forall x. ILan (g x -> a) (a -> g x) (h x)

ilan :: h a -> ILan g h (g a)
ilan x = ILan id id x

instance Invariant (ILan g h) where
    invmap f g (ILan h k x) = ILan (f . h) (k . g) x

instance HFunctor (ILan g) where
    hmap f (ILan h k x) = ILan h k (f x)

instance HTraversable (ILan g) where
    htraverse f (ILan g h x) = ILan g h <$> f x

instance HTraversable1 (ILan g) where
    htraverse1 f (ILan g h x) = ILan g h <$> f x

interpretILan
    :: Invariant f
    => (forall x. h x -> f (g x))
    -> ILan g h a
    -> f a
interpretILan f (ILan g h x) = invmap g h (f x)

interpretCoILan
    :: Functor f
    => (forall x. h x -> f (g x))
    -> ILan g h a
    -> f a
interpretCoILan f = unwrapFunctor . interpretILan (WrapFunctor . f)

interpretContraILan
    :: Contravariant f
    => (forall x. h x -> f (g x))
    -> ILan g h a
    -> f a
interpretContraILan f = unwrapContravariant . interpretILan (WrapContravariant . f)

