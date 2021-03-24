{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedLabels           #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}


module Typescript.Json.Types (
    TSPrim(..)
  , TSNamedPrim(..)
  , EnumLit(..)
  , TSType(..)
  , TSType_(..)
  , TSNamed(..)
  , TSNamed_(..)
  , withTSNamed_
  , TSNameable(..)
  , ObjMember(..)
  , TSKeyVal
  , mapTSType_
  , withTSType_
  , onTSType_
  , decideTSType_
  , IsObjType(..)
  , SIsObjType(..)
  , SNat_(..)
  , eqTSPrim
  , interpretObjMember
  , tsObjType
  , collapseIsObj
  , splitKeyVal
  , unNullable
  -- * Generics
  , TSTypeF(..)
  , TSTypeF_(..)
  , TSApplied(..)
  , TSAppliedF(..)
  , mapTSTypeF_
  , withTSTypeF_
  , ParseErr(..)
  , tsApply
  , tsApply1
  , tsApplyF
  , toParams
  , tsApplyVar
  , tsfParams
  , tsShift
  , shiftApplied
  , shiftAppliedF
  , shiftNameable
  , shiftTypeF
  ) where

import           Control.Applicative.Free
import           Control.Monad
import           Data.Fin                                  (Fin(..))
import           Data.Functor
import           Data.Functor.Apply
import           Data.Functor.Apply.Free
import           Data.Functor.Combinator hiding            (Comp(..))
import           Data.Functor.Contravariant.Divisible.Free (Dec1(..))
import           Data.Functor.Invariant
import           Data.GADT.Show
import           Data.HFunctor.Route
import           Data.Kind
import           Data.Map                                  (Map)
import           Data.SOP                                  (NP(..), K(..))
import           Data.Scientific                           (Scientific)
import           Data.Some                                 (Some(..))
import           Data.Text                                 (Text)
import           Data.Type.Equality
import           Data.Type.Nat
import           Data.Vec.Lazy                             (Vec(..))
import           Data.Void
import           Typescript.Json.Types.Combinators
import           Typescript.Json.Types.SNat
import qualified Control.Applicative.Lift                  as Lift
import qualified Data.Aeson                                as A
import qualified Data.Map                                  as M
import qualified Data.SOP                                  as SOP
import qualified Prettyprinter                             as PP

data EnumLit = ELString Text | ELNumber Scientific
  deriving (Show, Eq, Ord)

data TSPrim :: Type -> Type where
    TSBoolean    :: TSPrim Bool
    TSNumber     :: TSPrim Scientific
    TSBigInt     :: TSPrim Integer
    TSString     :: TSPrim Text
    TSStringLit  :: Text -> TSPrim ()
    TSNumericLit :: Scientific -> TSPrim ()
    TSBigIntLit  :: Integer    -> TSPrim ()
    TSUnknown    :: TSPrim A.Value
    TSAny        :: TSPrim A.Value
    TSVoid       :: TSPrim ()
    TSUndefined  :: TSPrim ()
    TSNull       :: TSPrim ()
    TSNever      :: TSPrim Void

deriving instance Show (TSPrim a)
deriving instance Eq (TSPrim a)
deriving instance Ord (TSPrim a)

instance GShow TSPrim where
    gshowsPrec = showsPrec

-- | "Named" primitive types, that cannot be anonymous
data TSNamedPrim :: Type -> Type where
    TSEnum       :: Vec n (Text, EnumLit) -> TSNamedPrim (Fin n)

deriving instance Show (TSNamedPrim a)
deriving instance Eq (TSNamedPrim a)
deriving instance Ord (TSNamedPrim a)

instance GShow TSNamedPrim where
    gshowsPrec = showsPrec

data TSType_ p a = forall k. TSType_ { unTSType_ :: TSType p k a }

instance Invariant (TSType_ p) where
    invmap f g = mapTSType_ (invmap f g)

-- TODO: technically the key can be an Int? { [n : number]: unknown }
data ObjMember f a = ObjMember
    { objMemberKey :: Text
    , objMemberVal :: (f :+: ILan Maybe f) a
    }

instance HFunctor ObjMember where
    hmap f (ObjMember k v) = ObjMember k (hbimap f (hmap f) v)

instance HTraversable ObjMember where
    htraverse f (ObjMember k v) = ObjMember k <$>
      case v of
        L1 x -> L1 <$> f x
        R1 y -> R1 <$> htraverse f y

instance Invariant f => Invariant (ObjMember f) where
    invmap f g (ObjMember x y) = ObjMember x (invmap f g y)

data IsObjType = NotObj | IsObj

data SIsObjType :: IsObjType -> Type where
    SNotObj :: SIsObjType 'NotObj
    SIsObj  :: SIsObjType 'IsObj

type TSKeyVal p = PreT Ap (ObjMember (TSType_ p))

data TSType :: Nat -> IsObjType -> Type -> Type where
    TSArray        :: ILan [] (TSType p k) a -> TSType p 'NotObj a
    -- this doesn't really make sense nakedly, but it's used internally
    -- a lot.  It's a bit like TSSingle, maybe.  but also maybe i wonder if
    -- tssingle, tsnullabe, and tsnfunc should all be commutative.
    -- also because it doesn't make sense nakedly, is its k param returned
    -- meaningful?
    --
    -- OKAY so, there is a good evidence that this behaves like 'IsObj,
    -- because it needs to be comparable across different fields in an
    -- object (nullable vs non-nullable same version)
    TSNullable     :: ILan Maybe (TSType p k) a -> TSType p 'NotObj a
    TSTuple        :: PreT Ap (TSType_ p) a -> TSType p 'NotObj a
    TSObject       :: TSKeyVal p a -> TSType p 'IsObj a
    TSSingle       :: TSType p 'IsObj a -> TSType p 'NotObj a
    TSUnion        :: PostT Dec1 (TSType_ p) a -> TSType p 'NotObj a
    TSNamedType    :: TSApplied p k a -> TSType p k a
    TSVar          :: !(Fin p) -> TSType p 'NotObj a   -- is NotObj right?
    TSIntersection :: PreT Ap1 (TSType p 'IsObj) a -> TSType p 'IsObj a
    TSPrimType     :: PS TSPrim a -> TSType p 'NotObj a

data TSNameable :: Nat -> IsObjType -> [Type] -> Type -> Type where
    TSNFunc     :: TSTypeF p k as a -> TSNameable p k as a
    TSNPrimType :: PS TSNamedPrim a -> TSNameable p 'NotObj '[] a
    -- REMOVED: use a named Any instead, and remove it from the exports
    -- TSNExternal :: PS ((:~:) A.Value) a -> TSNameable p 'NotObj '[] a

instance Invariant (TSNameable p k as) where
    invmap f g = \case
      TSNFunc x     -> TSNFunc (invmap f g x)
      TSNPrimType x -> TSNPrimType (invmap f g x)

data TSNamed_ p as a = forall k. TSNamed_ (TSNamed p k as a)


data TSNamed p k as a = TSNamed
    { tsnName :: Text
    , tsnType :: TSNameable p k as a
    }

instance Invariant (TSNamed p k as) where
    invmap f g (TSNamed n t) = TSNamed n (invmap f g t)

instance Invariant (TSNamed_ p as) where
    invmap f g (TSNamed_ x) = TSNamed_ (invmap f g x)

data TSTypeF :: Nat -> IsObjType -> [Type] -> Type -> Type where
    -- TODO: the next big thing: this must support "extends"
    -- semantics: anything "named" (er no, only interfaces) can be extended with an interface
    -- but also anything that is a parameter can require an interface
    -- so extends happens in two places:
    --
    -- 1. when declaring something with a name, so as a field in these
    -- constructors.  hm actaully wait it looks like for X extends Y, it
    -- only is allowed when X is an interface.  Y only needs to be an
    -- object. so that means it really can
    -- go only in TSGenericInterface.  neato. And it could pretty much be like an
    -- intersection type, it adds to the fields.
    --
    -- The rule is: "An interface can only extend an object type or
    -- intersection of object types with statically known members.
    -- "
    --
    -- DONE
    --
    -- 2. as a requirement for a paraemeter...so would have to go in NP (K
    -- Text) as?  And then so should we make it a type error if we use it
    -- in a case where it does not actually extend?  that means we have to
    -- have a type specifically only for interfaces?  or should extends
    -- always be to just a name, that is "inactive"?  yeah, actually hm.
    -- does it ever actually matter?  could the extending thing always just
    -- be a no-thing?  even in that case though, it chances that type to be
    -- an Object now, if it is extended.
    --
    -- okay, so does extending really matter?  hm yeah, we *could* make it
    -- matter if we do a check on the application.  like the application
    -- might yield Nothing
    --
    -- actually after some testing it seems like for Thing<X extends Y>,
    -- Y can really be anything. what does that even mean?
    --
    -- the error message seems to imply Y is some kind of constrataint:
    -- "Type 'X' does not satisfy the constraint 'Y'"
    --
    -- ooh fancy: function getProperty<Type, Key extends keyof Type>(obj:
    -- Type, key: Key) {
    -- https://www.typescriptlang.org/docs/handbook/2/generics.html
    --
    -- hm, testing to return Bool might not work because we want to have
    -- a "verified" version such that any TSNamedType is going to be
    -- valid.
    --
    -- oh no :( i guess it has to be a "smart constructor".  maybe we
    -- should smart-constructorize the object keys too
    --
    -- but this doesn't work for the generic deriving mechanisms,
    -- then...since they return Nothing/Just "dynamically", hm.
    --
    -- well, i guess we can say that the generics mechanisms are "safe"
    -- because they will never insert an extends
    --
    -- https://basarat.gitbook.io/typescript/type-system/type-compatibility
    TSGeneric
        -- ok so essentially the change will be...change this from K Text
        -- to something that includes an "extending"...and with the type
        -- parameter...oh! maybe we could even make it require to be
        -- extendable here by requiring the a -> Either text b?  nah hm.
        -- maybe just simple type.
        :: NP (K Text) as
        -- oh hey! proof of assignability can go here!!
        -- we can have it take NP (Proof (Plus r p)) as
        -- data Proof p a = forall b. Proof
        --    { pType   :: TSType_ p b
        --    , pAssign :: a -> Either Text b
        --    }
        -- and this can only be created if it is truly extensible!
        --
        -- we could even do an "unsafe" version, since pAssign is
        -- essentially ignored anyway.
        --
        -> (forall r. SNat_ r -> NP (TSType_ (Plus r p)) as -> TSType (Plus r p) k b)
        -> TSTypeF p k as b
    TSGenericInterface
        :: NP (K Text) as
        -> (a -> b -> c)            -- ^ day convolution: combine base and new
        -> (c -> (a, b))
        -> Lift (TSAppliedF p 'IsObj as) a
        -> (forall r. SNat_ r -> NP (TSType_ (Plus r p)) as -> TSKeyVal (Plus r p) b)
        -> TSTypeF p 'IsObj as c

data TSApplied p k a = forall as. (:$)
    { tsaFunc :: TSNamed p k as a
    , tsaArgs :: NP (TSType_ p) as
    }

data TSAppliedF p k as a = forall bs. (:?)
    { tsafFunc :: TSNamed p k bs a
    , tsafArgs :: NP (TSTypeF_ p as) bs
    }

instance Invariant (TSTypeF p k as) where
    invmap f g (TSGeneric xs h) =
        TSGeneric xs (\q -> invmap f g . h q)
    invmap f g (TSGenericInterface xs fe ef ext h) =
        TSGenericInterface xs (\x y -> f (fe x y)) (ef . g) ext h

data TSTypeF_ p as b = forall k. TSTypeF_ { unTSTypeF_ :: TSTypeF p k as b }

instance Invariant (TSTypeF_ p as) where
    invmap f g (TSTypeF_ x) = TSTypeF_ (invmap f g x)

instance Invariant (TSType p k) where
    invmap f g = \case
      TSArray  t  -> TSArray (invmap f g t )
      TSNullable t -> TSNullable (invmap f g t)
      TSTuple  ts -> TSTuple (invmap f g ts)
      TSObject ts -> TSObject (invmap f g ts)
      TSSingle ts -> TSSingle (invmap f g ts)
      TSUnion  ts -> TSUnion (invmap f g ts)
      TSNamedType (TSNamed nm nt :$ xs) -> case nt of
        TSNFunc tf     -> TSNamedType $ TSNamed nm (TSNFunc     (invmap f g tf)) :$ xs
        TSNPrimType ps -> TSNamedType $ TSNamed nm (TSNPrimType (invmap f g ps)) :$ xs
      TSVar i -> TSVar i
      TSIntersection ts -> TSIntersection (invmap f g ts)
      TSPrimType p -> TSPrimType (invmap f g p)

data ParseErr = PEInvalidEnum    [(Text, EnumLit)]
              | PEInvalidString  Text       Text
              | PEInvalidNumber  Scientific Scientific
              | PEInvalidBigInt  Integer    Integer
              | PEPrimitive      (Some TSPrim) Text
              | PENamedPrimitive Text (Some TSNamedPrim) Text
              | PEExtraTuple     Int        Int
              | PENotInUnion     [PP.Doc ()]
              | PENever
  deriving (Show)

withTSType_
    :: (forall k. TSType p k a -> r)
    -> TSType_ p a
    -> r
withTSType_ f (TSType_ t) = f t

mapTSType_
    :: (forall k. TSType p k a -> TSType us k b)
    -> TSType_ p a
    -> TSType_ us b
mapTSType_ f = withTSType_ (TSType_ . f)

withTSTypeF_
    :: (forall k. TSTypeF p k as b -> r)
    -> TSTypeF_ p as  b
    -> r
withTSTypeF_ f (TSTypeF_ x) = f x

mapTSTypeF_
    :: (forall k. TSTypeF p k as b -> TSTypeF q k as' b')
    -> TSTypeF_ p as  b
    -> TSTypeF_ q as' b'
mapTSTypeF_ f = withTSTypeF_ (TSTypeF_ . f)

withTSNamed_
    :: (forall k. TSNamed p k as a -> r)
    -> TSNamed_ p as a
    -> r
withTSNamed_ f (TSNamed_ t) = f t

eqTSPrim :: TSPrim a -> TSPrim b -> Maybe (a :~: b)
eqTSPrim = \case
    TSBoolean -> \case
      TSBoolean -> Just Refl
      _ -> Nothing
    TSNumber -> \case
      TSNumber -> Just Refl
      _ -> Nothing
    TSBigInt -> \case
      TSBigInt -> Just Refl
      _ -> Nothing
    TSString -> \case
      TSString -> Just Refl
      _ -> Nothing
    TSStringLit x -> \case
      TSStringLit y -> Refl <$ guard (x == y)
      _ -> Nothing
    TSNumericLit x -> \case
      TSNumericLit y -> Refl <$ guard (x == y)
      _ -> Nothing
    TSBigIntLit x -> \case
      TSBigIntLit y -> Refl <$ guard (x == y)
      _ -> Nothing
    TSUnknown -> \case
      TSUnknown -> Just Refl
      _ -> Nothing
    TSAny -> \case
      TSAny -> Just Refl
      _ -> Nothing
    TSVoid -> \case
      TSVoid -> Just Refl
      _ -> Nothing
    TSUndefined -> \case
      TSUndefined -> Just Refl
      _ -> Nothing
    TSNull -> \case
      TSNull -> Just Refl
      _ -> Nothing
    TSNever -> \case
      TSNever -> Just Refl
      _ -> Nothing

interpretObjMember
    :: Invariant g
    => (Text -> f ~> g)
    -> (forall x. Text -> f x -> g (Maybe x))
    -> ObjMember f ~> g
interpretObjMember f g (ObjMember k v) = case v of
    L1 x -> f k x
    R1 y -> interpretILan (g k) y

tsApply
    :: TSTypeF p k as b      -- ^ type function
    -> NP (TSType_ p) as     -- ^ thing to apply
    -> TSType p k b
tsApply (TSGeneric _ f) t = f SZ_ t
tsApply (TSGenericInterface _ fe ef ext f) t = case ext of
    Lift.Pure  x -> invmap (fe x) (snd . ef) $ TSObject (f SZ_ t)
    Lift.Other (TSNamed _ (TSNFunc tf) :? qs) -> TSObject . PreT $
        fe <$> hmap (mapPre (fst . ef)) (unPreT $ collapseIsObj (tsApplyF tf qs t))
           <.> hmap (mapPre (snd . ef)) (unPreT $ f SZ_ t)

tsApplyF
    :: TSTypeF p k as b
    -> NP (TSTypeF_ p bs) as
    -> NP (TSType_ p) bs
    -> TSType p k b
tsApplyF tf qs rs = tf `tsApply` hmap (withTSTypeF_ (TSType_ . (`tsApply` rs))) qs

tsApply1
    :: TSTypeF p k '[a] b      -- ^ type function
    -> TSType_ p a         -- ^ thing to apply
    -> TSType p k b
tsApply1 f t = tsApply f (t :* Nil)

toParams
    :: NP (K Text) as
    -> (SNat_ (Length as), NP (K (Fin (Length as))) as)
toParams = \case
    Nil -> (SZ_, Nil)
    K _ :* ps -> case toParams ps of
      (n, qs) -> (SS_ n, K FZ :* hmap (K . FS . SOP.unK) qs)

-- shadowing?

-- | Apply a TypeF with free variables
tsApplyVar
    :: forall p k as b. ()
    => TSTypeF p k as b
    -> TSType (Plus (Length as) p) k b
tsApplyVar (TSGeneric ps g) =
    g n (hmap (TSType_ . TSVar . weakenFin @_ @p . SOP.unK) es)
  where
    (n, es) = toParams ps
tsApplyVar (TSGenericInterface ps fe ef ext g) = case ext of
    Lift.Pure x -> invmap (fe x) (snd . ef) . TSObject $
      g n (hmap (TSType_ . TSVar . weakenFin @_ @p . SOP.unK) es)
    Lift.Other (TSNamed _ (TSNFunc tf) :? qs) -> TSObject . PreT $
      fe <$> hmap (mapPre (fst . ef))
               (unPreT . collapseIsObj $
                  tsApplyF
                    (shiftTypeF n tf)
                    (hmap (mapTSTypeF_ (shiftTypeF n)) qs)
                    (hmap (TSType_ . TSVar . weakenFin @_ @p . SOP.unK) es)
               )
         <.> hmap (mapPre (snd . ef))
               (unPreT . g n $
                  hmap (TSType_ . TSVar . weakenFin @_ @p . SOP.unK) es
               )
  where
    (n, es) = toParams ps

tsfParams :: TSTypeF p k as b -> Vec (Length as) Text
tsfParams = \case
    TSGeneric ps _ -> prodVec ps
    TSGenericInterface ps _ _ _ _ -> prodVec ps

collapseIsObj :: TSType p 'IsObj a -> TSKeyVal p a
collapseIsObj = \case
    TSObject kv -> kv
    TSNamedType (TSNamed _ (TSNFunc tf) :$ xs) -> collapseIsObj $ tsApply tf xs
    TSIntersection (PreT xs) -> PreT $ interpret (\(f :>$<: x) -> hmap (mapPre f) . unPreT $ collapseIsObj x) xs

tsShift
    :: forall r p k a. ()
    => SNat_ r
    -> TSType p k a
    -> TSType (Plus r p) k a
tsShift n = go
  where
    go :: forall q j b. TSType q j b -> TSType (Plus r q) j b
    go = \case
      TSArray ts -> TSArray (hmap go ts)
      TSNullable ts -> TSNullable (hmap go ts)
      TSTuple ts -> TSTuple (hmap (mapTSType_ go) ts)
      TSUnion ts -> TSUnion (hmap (mapTSType_ go) ts)
      TSObject ts -> TSObject (hmap (hmap (mapTSType_ go)) ts)
      TSSingle t  -> TSSingle (go t)
      TSNamedType a -> TSNamedType (shiftApplied n a)
      TSIntersection t -> TSIntersection (hmap go t)
      TSVar i    -> TSVar (shiftFin n i)
      TSPrimType t -> TSPrimType t

shiftApplied :: SNat_ r -> TSApplied p k a -> TSApplied (Plus r p) k a
shiftApplied n (TSNamed nm nt :$ xs) =
        TSNamed nm (shiftNameable n nt)
     :$ hmap (mapTSType_ (tsShift n)) xs

shiftAppliedF :: SNat_ r -> TSAppliedF p k as a -> TSAppliedF (Plus r p) k as a
shiftAppliedF n (TSNamed nm nt :? xs) =
        TSNamed nm (shiftNameable n nt)
     :? hmap (mapTSTypeF_ (shiftTypeF n)) xs

shiftNameable :: SNat_ r -> TSNameable p k as a -> TSNameable (Plus r p) k as a
shiftNameable n = \case
    TSNFunc tf     -> TSNFunc (shiftTypeF n tf)
    TSNPrimType ps -> TSNPrimType ps

shiftTypeF :: forall r p k as a. SNat_ r -> TSTypeF p k as a -> TSTypeF (Plus r p) k as a
shiftTypeF n = \case
    TSGeneric ps f -> TSGeneric ps $ \q -> case assocPlus @_ @r @p q of
      Refl -> f (plusNat q n)
    TSGenericInterface ps fe ef ext f ->
        let m = vecToSNat_ (prodVec ps)
        in TSGenericInterface ps fe ef
             (case assocPlus @_ @(Length as) @p n of
                Refl -> case commutePlus n m of
                  Refl -> case assocPlus @_ @r @p m of
                    Refl -> (hmap (shiftAppliedF n) ext)
             )
             (\q -> case assocPlus @_ @r @p q of Refl -> f (plusNat q n))

tsObjType
    :: TSType p k a
    -> SIsObjType k
tsObjType = \case
    TSArray  _                    -> SNotObj
    TSNullable _                  -> SNotObj
    TSTuple  _                    -> SNotObj
    TSObject _                    -> SIsObj
    TSSingle _                    -> SNotObj
    TSUnion  _                    -> SNotObj
    TSNamedType (TSNamed _ nt :$ _)     -> case nt of
      TSNFunc tsf@(TSGeneric{})      -> tsObjType (tsApplyVar tsf)
      TSNFunc (TSGenericInterface{}) -> SIsObj
      TSNPrimType _                  -> SNotObj
    TSVar _                       -> SNotObj
    TSIntersection _              -> SIsObj
    TSPrimType _                  -> SNotObj


onTSType_
    :: (TSType p 'NotObj a -> r)
    -> (TSType p 'IsObj  a -> r)
    -> TSType_ p a
    -> r
onTSType_ f g (TSType_ t) = case tsObjType t of
    SNotObj -> f t
    SIsObj  -> g t

decideTSType_ :: TSType_ p ~> (TSType p 'NotObj :+: TSType p 'IsObj)
decideTSType_ = onTSType_ L1 R1

splitKeyVal :: TSKeyVal p a -> Map Text (Some (Pre a (TSType_ p)))
splitKeyVal (PreT p) = M.fromList $ splitAp p <&> \case
    Some (q :>$<: ObjMember{..}) ->
      ( objMemberKey
      , case objMemberVal of
          L1 z -> Some $ q :>$<: z
          R1 (ILan f g (TSType_ w)) -> Some $
            q :>$<: TSType_ (TSNullable (ILan f g w))
      )

-- | converts a Nullable x to x | null
unNullable :: ILan Maybe (TSType p k) a -> TSType p 'NotObj a
unNullable (ILan f g t) = TSUnion $ PostT $
    Dec1 (maybe (Right ()) Left . g) (f . Just :<$>: TSType_ t) $
      injectPost (\_ -> f Nothing) $ TSType_ (TSPrimType (inject TSNull))

