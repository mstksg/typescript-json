{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeOperators             #-}

module Typescript.Json.Types.Combinators (
    PS(..)
  , ILan(..)
  , ilan
  , interpretILan
  , interpretCoILan
  , interpretContraILan
  , MP(..)
  , NP2(..)
  , hmap2
  , htraverse2
  , hfoldMap2
  , np2Left
  , splitAp
  ) where

import           Control.Applicative.Free
import           Data.Functor.Combinator
import           Data.Functor.Contravariant
import           Data.Functor.Invariant
import           Data.Kind
import           Data.SOP
import           Data.Some                  (Some(..))
import           Data.Text                  (Text)

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

splitAp :: forall f b. Ap f b -> [Some f]
splitAp = go
  where
    go :: Ap f c -> [Some f]
    go = \case
      Pure _ -> []
      Ap x xs -> Some x : go xs

data MP :: (k -> Type) -> Maybe k -> Type where
    MPNothing :: MP f 'Nothing
    MPJust :: f a -> MP f ('Just a)

instance HFunctor MP where
    hmap f = \case
      MPNothing -> MPNothing
      MPJust x -> MPJust (f x)

instance HTraversable MP where
    htraverse f = \case
      MPNothing -> pure MPNothing
      MPJust x -> MPJust <$> f x

data NP2 :: (k -> j -> Type) -> [k] -> [j] -> Type where
    Nil2 :: NP2 f '[] '[]
    (:**) :: f a b -> NP2 f as bs -> NP2 f (a ': as) (b ': bs)
infixr 5 :**

hmap2 :: forall f g as bs. (forall a b. f a b -> g a b) -> NP2 f as bs -> NP2 g as bs
hmap2 f = go
  where
    go :: NP2 f cs ds -> NP2 g cs ds
    go = \case
      Nil2 -> Nil2
      x :** xs -> f x :** go xs

htraverse2 :: forall f g h as bs. Applicative h => (forall a b. f a b -> h (g a b)) -> NP2 f as bs -> h (NP2 g as bs)
htraverse2 f = go
  where
    go :: NP2 f cs ds -> h (NP2 g cs ds)
    go = \case
      Nil2 -> pure Nil2
      x :** xs -> (:**) <$> f x <*> go xs

hfoldMap2 :: forall f m as bs. Monoid m => (forall a b. f a b -> m) -> NP2 f as bs -> m
hfoldMap2 f = unK . htraverse2 (K . f)

np2Left :: forall f g as bs. (forall a b. f a b -> g a) -> NP2 f as bs -> NP g as
np2Left f = go
  where
    go :: NP2 f cs ds -> NP g cs
    go = \case
      Nil2 -> Nil
      x :** xs -> f x :* go xs
