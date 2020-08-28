{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Typescript.Json where

import           Data.Bifunctor
import           Data.Functor.Combinator hiding (Comp(..))
import           Data.Functor.Invariant
import           Data.Proxy
import           Data.SOP                       (NP(..), NS(..), I(..), K(..), (:.:)(..))
import           Data.Type.Equality
import           Data.Void
import           GHC.TypeLits
import           Typescript.Json.Core
import qualified Data.Bifunctor.Assoc           as B
import qualified Data.SOP                       as SOP

class KnownNotElem ks k where
    knownNotElem :: Elem ks k -> Void

instance KnownNotElem '[] k where
    knownNotElem = \case{}

type family CmpEq (a :: Ordering) :: Bool where
    CmpEq 'LT = 'False
    CmpEq 'EQ = 'True
    CmpEq 'GT = 'False

instance (CmpEq (CmpSymbol k j) ~ 'False, KnownNotElem ks j) => KnownNotElem (k ': ks) j where
    knownNotElem = \case
      ES x -> knownNotElem x

instance (CmpEq (CmpNat k j) ~ 'False, KnownNotElem ks j) => KnownNotElem (k ': ks) j where
    knownNotElem = \case
      ES x -> knownNotElem x

knownNotElems :: forall js ks. SOP.All (KnownNotElem js) ks => NP (Not :.: Elem js) ks
knownNotElems = SOP.hcpure (Proxy @(KnownNotElem js)) $ Comp (Not knownNotElem)

injectKCO :: Key k -> f a -> KeyChain '[k] f (Maybe a)
injectKCO k x = KCCons const (,()) (\case {}) (Keyed k (R1 (ilan x))) (KCNil ())

kcCons
    :: KnownNotElem ks k
    => Key k
    -> (a -> b -> c)
    -> (c -> (a, b))
    -> f a
    -> KeyChain ks f b
    -> KeyChain (k ': ks) f c
kcCons k f g x = KCCons f g knownNotElem (Keyed k (L1 x))

concatNotElem
    :: forall js ks a p. ()
    => NP p js
    -> (Elem js a -> Void)
    -> (Elem ks a -> Void)
    -> (Elem (js ++ ks) a -> Void)
concatNotElem = \case
    Nil     -> \_ g -> g
    _ :* ps -> \f g -> \case
      EZ   -> f EZ
      ES e -> concatNotElem ps (f . ES) g e

appendKeyChain
    :: forall a b c f ks js. ()
    => (a -> b -> c)
    -> (c -> (a, b))
    -> NP (Not :.: Elem js) ks
    -> KeyChain ks f a
    -> KeyChain js f b
    -> KeyChain (ks ++ js) f c
appendKeyChain f g = \case
    Nil -> \case
      KCNil x -> invmap (f x) (snd . g)
    Comp (Not n) :* ns -> \case
      KCCons h k m x xs ->
         KCCons         (\a (b, c) -> f (h a b) c) (B.assoc . first k . g) (concatNotElem ns m n)  x
       . appendKeyChain (,)                        id                      ns                      xs

takeNP
    :: forall as bs p q. ()
    => NP p as
    -> NP q (as ++ bs)
    -> (NP (p :*: q) as, NP q bs)
takeNP = \case
    Nil -> (Nil,)
    x :* xs -> \case
      y :* ys -> first ((x :*: y) :*) (takeNP xs ys)

appendIntersections
    :: forall a b c n ks js ps. ()
    => (a -> b -> c)
    -> (c -> (a, b))
    -> NP (Not :.: Elem js) ks
    -> Intersections ps ks n a
    -> Intersections ps js n b
    -> Intersections ps (ks ++ js) n c
appendIntersections f g ns = \case
    INil x -> invmap (f x) (snd . g)
    ICons h k ms (x :: TSType ps ('Just as) n q) (xs :: Intersections ps bs n r) -> case takeNP @as @bs ms ns of
      (here, there) ->
        case assocConcat @as @bs @js here of
          Refl -> ICons               (\a (b, c) -> f (h a b) c) (B.assoc . first k . g) (concatNotElem' there here) x
                . appendIntersections (,) id there xs

injectIntersection :: TSType ps ('Just as) n a -> Intersections ps as n a
injectIntersection x = case appendNil ks of
    Refl -> ICons const (,()) (hmap (\_ -> Comp (Not (\case {}))) ks) x (INil ())
  where
    ks = typeStructure x

intersectionsKeys
    :: Intersections ps ks n a
    -> NP Key ks
intersectionsKeys = \case
    INil _ -> Nil
    ICons _ _ _ x xs -> typeStructure x `appendNP` intersectionsKeys xs

typeStructure :: TSType ps ('Just as) n a -> NP Key as
typeStructure = \case
    TSObject _ ts -> keyChainKeys ts
    TSIntersection ts -> intersectionsKeys ts
    TSNamed _ t -> typeStructure t
    TSGeneric _ _ t -> typeStructure t

assocConcat
    :: forall as bs cs p. ()
    => NP p as
    -> ((as ++ bs) ++ cs) :~: (as ++ (bs ++ cs))
assocConcat = \case
    Nil -> Refl
    _ :* ps -> case assocConcat @_ @bs @cs ps of
      Refl -> Refl

appendNil
    :: NP p as
    -> (as ++ '[]) :~: as
appendNil = \case
    Nil -> Refl
    _ :* ps -> case appendNil ps of
      Refl -> Refl

concatNotElem'
    :: forall js ks as p. ()
    => NP p js
    -> NP ((Not :.: Elem js) :*: (Not :.: Elem ks)) as
    -> NP (Not :.: Elem (js ++ ks)) as
concatNotElem' js = hmap $ \(Comp (Not ns) :*: Comp (Not ms)) ->
    Comp $ Not $ concatNotElem js ns ms

appendNP :: NP f as -> NP f bs -> NP f (as ++ bs)
appendNP = \case
    Nil -> id
    x :* xs -> (x :*) . appendNP xs

