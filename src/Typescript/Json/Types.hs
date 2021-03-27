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
  , TSBase(..)
  , EnumLit(..)
  , TSType(..)
  , TSType_(..)
  , TSNamed(..)
  , TSNamed_(..)
  , withTSNamed_
  , Assign(..)
  , TSNameable(..)
  , Param(..)
  , Arg(..)
  , Arg_(..)
  , withArg_
  , ObjMember(..)
  , TSKeyVal
  , mapTSType_
  , withTSType_
  , onTSType_
  , decideTSType_
  , IsObjType(..)
  , SIsObjType(..)
  , SNat_(..)
  , interpretObjMember
  , tsObjType
  , collapseIsObj
  , splitKeyVal
  -- , unNullable
  , toNullable
  , toVarArgs
  -- * Generics
  , TSTypeF(..)
  , TSTypeF_(..)
  , TSApplied(..)
  , TSAppliedF(..)
  , ArgF(..)
  , ArgF_(..)
  , withArgF_
  , mapTSTypeF_
  , withTSTypeF_
  , pattern Param'
  , pattern Arg'
  , ParseErr(..)
  , tsApply
  , tsApply1
  , tsApplyF
  -- , toParams
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
import           Data.Bifunctor
import           Data.Fin                                  (Fin(..))
import           Data.Functor
import           Data.Functor.Apply
import           Data.Functor.Apply.Free
import           Data.Functor.Combinator hiding            (Comp(..))
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divisible.Free (Dec1(..), Dec(..))
import           Data.Functor.Invariant
import           Data.Functor.Invariant.DecAlt
import           Data.Functor.Invariant.DivAp
import           Data.GADT.Show
import           Data.HFunctor.Route
import           Data.Kind
import           Data.Map                                  (Map)
import           Data.Profunctor
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
import qualified Data.Functor.Invariant.Night              as I
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

data TSBase :: Type -> Type where
    TSVoid       :: TSBase ()
    TSUndefined  :: TSBase ()
    TSNull       :: TSBase ()
    TSNever      :: TSBase Void

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
    --
    -- TODO: so i think maybe this is a bad idea in general, and we should
    -- just have an "is nullable" check to squish records.  but now in this
    -- case that means that we can't use | null for the Maybe instance, it
    -- should probably be an Option type.  that's because we should NOT
    -- rely on (Nullable x) | null being any different than x | null...way
    -- too fragile
    TSTuple        :: PreT Ap (TSType_ p) a -> TSType p 'NotObj a
    TSObject       :: TSKeyVal p a -> TSType p 'IsObj a
    TSSingle       :: TSType p 'IsObj a -> TSType p 'NotObj a
    TSUnion        :: PostT Dec1 (TSType_ p) a -> TSType p 'NotObj a
    TSNamedType    :: TSApplied p k a -> TSType p k a
    TSVar          :: !(Fin p) -> TSType p 'NotObj a   -- is NotObj right?
    TSIntersection :: PreT Ap1 (TSType p 'IsObj) a -> TSType p 'IsObj a
    TSPrimType     :: PS TSPrim a -> TSType p 'NotObj a
    TSBaseType     :: ICoyoneda TSBase a -> TSType p 'NotObj a

data TSNameable :: Nat -> IsObjType -> [Type] -> [Maybe Type] -> Type -> Type where
    TSNFunc     :: TSTypeF p k as es a -> TSNameable p k as es a
    TSNPrimType :: PS TSNamedPrim a -> TSNameable p 'NotObj '[] '[] a

instance Invariant (TSNameable p k as es) where
    invmap f g = \case
      TSNFunc x     -> TSNFunc (invmap f g x)
      TSNPrimType x -> TSNPrimType (invmap f g x)

data TSNamed_ p as es a = forall k. TSNamed_ (TSNamed p k as es a)


data TSNamed p k as es a = TSNamed
    { tsnName :: Text
    , tsnType :: TSNameable p k as es a
    }

instance Invariant (TSNamed p k as es) where
    invmap f g (TSNamed n t) = TSNamed n (invmap f g t)

instance Invariant (TSNamed_ p as es) where
    invmap f g (TSNamed_ x) = TSNamed_ (invmap f g x)

newtype Assign a b = Assign { runAssign :: a -> Either Text b }

data Param p a b = Param
    { paramName    :: Text
    , paramExtends :: MP (TSType_ p) b
    }

paramSimple :: Text -> Param p a 'Nothing
paramSimple t = Param t MPNothing

data Arg p k a b = Arg
    { argType   :: TSType p k a
    , argAssign :: MP (Assign a) b
    }

data Arg_ p a b = forall k. Arg_ (Arg p k a b)

withArg_
    :: (forall k. Arg p k a e -> r)
    -> Arg_ p a e
    -> r
withArg_ f (Arg_ x) = f x

argSimple :: TSType p k a -> Arg_ p a 'Nothing
argSimple t = Arg_ $ Arg t MPNothing

pattern Arg' :: TSType p k a -> Arg p k a 'Nothing
pattern Arg' t = Arg t MPNothing

pattern Param' :: Text -> Param p a 'Nothing
pattern Param' t = Param t MPNothing


data TSTypeF :: Nat -> IsObjType -> [Type] -> [Maybe Type] -> Type -> Type where
    TSGeneric
        :: NP2 (Param p) as es
        -> (forall r. SNat_ r -> NP2 (Arg_ (Plus r p)) as es -> TSType (Plus r p) k b)
        -> TSTypeF p k as es b
    TSGenericInterface
        :: NP2 (Param p) as es
        -> (a -> b -> c)            -- ^ covariant day convolution: combine base and new
        -> (c -> (a, b))            -- ^ contravariant day convolution: split into base and new
        -> Lift (TSAppliedF p 'IsObj as es) a
        -> (forall r. SNat_ r -> NP2 (Arg_ (Plus r p)) as es -> TSKeyVal (Plus r p) b)
        -> TSTypeF p 'IsObj as es c

data TSApplied p k a = forall as es. (:$)
    { tsaFunc :: TSNamed p k as es a
    , tsaArgs :: NP2 (Arg_ p) as es
    }

data TSAppliedF p k as es a = forall bs ds. (:?)
    { tsafFunc :: TSNamed p k bs ds a
    , tsafArgs :: NP2 (ArgF_ p as es) bs ds
    }

data ArgF p k as es a e = ArgF
    { argfType   :: TSTypeF p k as es a
    , argfAssign :: MP (Assign a) e
    }

data ArgF_ p as es a e = forall k. ArgF_ (ArgF p k as es a e)

withArgF_
    :: (forall k. ArgF p k as es a e -> r)
    -> ArgF_ p as es a e
    -> r
withArgF_ f (ArgF_ x) = f x

instance Invariant (TSTypeF p k as es) where
    invmap f g (TSGeneric xs h) =
        TSGeneric xs (\q -> invmap f g . h q)
    invmap f g (TSGenericInterface xs fe ef ext h) =
        TSGenericInterface xs (\x y -> f (fe x y)) (ef . g) ext h

data TSTypeF_ p as es b = forall k. TSTypeF_ { unTSTypeF_ :: TSTypeF p k as es b }

instance Invariant (TSTypeF_ p as es) where
    invmap f g (TSTypeF_ x) = TSTypeF_ (invmap f g x)

instance Invariant (TSType p k) where
    invmap f g = \case
      TSArray  t  -> TSArray (invmap f g t )
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
      TSBaseType p -> TSBaseType (invmap f g p)

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
    :: (forall k. TSTypeF p k as es b -> r)
    -> TSTypeF_ p as es b
    -> r
withTSTypeF_ f (TSTypeF_ x) = f x

mapTSTypeF_
    :: (forall k. TSTypeF p k as es b -> TSTypeF q k as' es' b')
    -> TSTypeF_ p as  es b
    -> TSTypeF_ q as' es' b'
mapTSTypeF_ f = withTSTypeF_ (TSTypeF_ . f)

withTSNamed_
    :: (forall k. TSNamed p k as es a -> r)
    -> TSNamed_ p as es a
    -> r
withTSNamed_ f (TSNamed_ t) = f t

interpretObjMember
    :: Invariant g
    => (Text -> f ~> g)
    -> (forall x. Text -> f x -> g (Maybe x))
    -> ObjMember f ~> g
interpretObjMember f g (ObjMember k v) = case v of
    L1 x -> f k x
    R1 y -> interpretILan (g k) y

tsApply
    :: TSTypeF p k as es b      -- ^ type function
    -> NP2 (Arg_ p) as es     -- ^ thing to apply
    -> TSType p k b
tsApply (TSGeneric _ f) t = f SZ_ t
tsApply (TSGenericInterface _ fe ef ext f) t = case ext of
    Lift.Pure  x -> invmap (fe x) (snd . ef) $ TSObject (f SZ_ t)
    Lift.Other (TSNamed _ (TSNFunc tf) :? qs) -> TSObject . PreT $
        fe <$> hmap (mapPre (fst . ef)) (unPreT $ collapseIsObj (tsApplyF tf qs t))
           <.> hmap (mapPre (snd . ef)) (unPreT $ f SZ_ t)

tsApplyF
    :: forall p k as es bs ds b. TSTypeF p k as es b
    -> NP2 (ArgF_ p bs ds) as es
    -> NP2 (Arg_ p) bs ds
    -> TSType p k b
tsApplyF tf qs rs = tf `tsApply` hmap2 (withArgF_ (Arg_ . go)) qs
  where
    go :: ArgF p j bs ds a c -> Arg p j a c
    go ArgF{..} = Arg
      { argType   = tsApply argfType rs
      , argAssign = argfAssign
      }

tsApply1
    :: TSTypeF p k '[a] '[e] b      -- ^ type function
    -> Arg_ p a e         -- ^ thing to apply
    -> TSType p k b
tsApply1 f t = tsApply f (t :** Nil2)

data TempArg n a b = TempArg
    { taIx     :: Fin n
    , taAssign :: MP (Assign a) b
    }

toVarArgs
    :: forall p as es. ()
    => NP2 (Param p) as es
    -> (SNat_ (Length as), NP2 (Arg_ (Plus (Length as) p)) as es)
toVarArgs = second (hmap2 typeUp) . go
  where
    go  :: NP2 (Param p) cs ds
        -> (SNat_ (Length cs), NP2 (TempArg (Length cs)) cs ds)
    go = \case
      Nil2 -> (SZ_, Nil2)
      Param{..} :** ps -> case go ps of
        (n, qs) ->
          ( SS_ n
          , TempArg FZ (hmap (const varAssign) paramExtends)
             :** hmap2 (\case TempArg x y -> TempArg (FS x) y) qs
          )
    typeUp :: TempArg (Length as) a e -> Arg_ (Plus (Length as) p) a e
    typeUp (TempArg i a) = Arg_ $ Arg (TSVar (weakenFin @_ @p i)) a
    varAssign = Assign $ \_ -> Left "Type variables can be assigned to anything"

-- shadowing?

-- | Apply a TypeF with free variables
tsApplyVar
    :: forall p k as es b. ()
    => TSTypeF p k as es b
    -> TSType (Plus (Length as) p) k b
tsApplyVar (TSGeneric ps g) = uncurry g (toVarArgs ps)
tsApplyVar (TSGenericInterface ps fe ef ext g) = case ext of
    Lift.Pure x -> invmap (fe x) (snd . ef) $ TSObject (g n es)
      -- g n (hmap (TSType_ . TSVar . weakenFin @_ @p . SOP.unK) es)
    Lift.Other (TSNamed _ (TSNFunc tf) :? qs) -> TSObject . PreT $
      fe <$> hmap (mapPre (fst . ef))
               (unPreT . collapseIsObj $
                  tsApplyF
                    (shiftTypeF n tf)
                    (hmap2 (withArgF_ (ArgF_ . shiftArgF n)) qs)
                    es
               )
         <.> hmap (mapPre (snd . ef)) (unPreT (g n es))
  where
    (n, es) = toVarArgs ps

tsfParams :: TSTypeF p k as es b -> Vec (Length as) Text
tsfParams = \case
    TSGeneric ps _ -> prodVec2 paramName ps
    TSGenericInterface ps _ _ _ _ -> prodVec2 paramName ps

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
      TSTuple ts -> TSTuple (hmap (mapTSType_ go) ts)
      TSUnion ts -> TSUnion (hmap (mapTSType_ go) ts)
      TSObject ts -> TSObject (hmap (hmap (mapTSType_ go)) ts)
      TSSingle t  -> TSSingle (go t)
      TSNamedType a -> TSNamedType (shiftApplied n a)
      TSIntersection t -> TSIntersection (hmap go t)
      TSVar i    -> TSVar (shiftFin n i)
      TSPrimType t -> TSPrimType t
      TSBaseType t -> TSBaseType t

shiftApplied :: SNat_ r -> TSApplied p k a -> TSApplied (Plus r p) k a
shiftApplied n (TSNamed nm nt :$ xs) =
        TSNamed nm (shiftNameable n nt)
     :$ hmap2 (withArg_ (Arg_ . shiftArg n)) xs
     -- :$ hmap (mapTSType_ (tsShift n)) xs

shiftAppliedF :: SNat_ r -> TSAppliedF p k as es a -> TSAppliedF (Plus r p) k as es a
shiftAppliedF n (TSNamed nm nt :? xs) =
        TSNamed nm (shiftNameable n nt)
     :? hmap2 (withArgF_ (ArgF_ . shiftArgF n)) xs
     -- :? hmap2 (mapTSTypeF_ (shiftTypeF n)) xs

shiftNameable :: SNat_ r -> TSNameable p k as es a -> TSNameable (Plus r p) k as es a
shiftNameable n = \case
    TSNFunc tf     -> TSNFunc (shiftTypeF n tf)
    TSNPrimType ps -> TSNPrimType ps

shiftTypeF :: forall r p k as es a. SNat_ r -> TSTypeF p k as es a -> TSTypeF (Plus r p) k as es a
shiftTypeF n = \case
    TSGeneric ps f -> TSGeneric (hmap2 (shiftParam n) ps) $ \q -> case assocPlus @_ @r @p q of
      Refl -> f (plusNat q n)
    TSGenericInterface ps fe ef ext f ->
        let m = vecToSNat_ (prodVec2 paramName ps)
        in TSGenericInterface (hmap2 (shiftParam n) ps) fe ef
             (case assocPlus @_ @(Length as) @p n of
                Refl -> case commutePlus n m of
                  Refl -> case assocPlus @_ @r @p m of
                    Refl -> (hmap (shiftAppliedF n) ext)
             )
             (\q -> case assocPlus @_ @r @p q of Refl -> f (plusNat q n))

shiftParam :: SNat_ r -> Param p a b -> Param (Plus r p) a b
shiftParam n Param{..} =
    Param { paramName
          , paramExtends = hmap (mapTSType_ (tsShift n)) paramExtends
          }

shiftArg :: SNat_ r -> Arg p k a e -> Arg (Plus r p) k a e
shiftArg n Arg{..} =
    Arg { argType = tsShift n argType
        , argAssign
        }

shiftArgF :: SNat_ r -> ArgF p k as es a e -> ArgF (Plus r p) k as es a e
shiftArgF n ArgF{..} =
    ArgF { argfType = shiftTypeF n argfType
         , argfAssign
         }

tsObjType
    :: TSType p k a
    -> SIsObjType k
tsObjType = \case
    TSArray  _                    -> SNotObj
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
    TSBaseType _                  -> SNotObj


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
            q :>$<: TSType_ (invmap f g (toNullable w))
      )

toNullable :: TSType p k a -> TSType p 'NotObj (Maybe a)
toNullable t = TSUnion . PostT $
    decide (maybe (Right ()) Left)
        (injectPost Just (TSType_ t))
        (injectPost (const Nothing) (TSType_ (TSBaseType (inject TSNull))))


data SuspendedDivAp f b a = SDA
    { sdProj  :: (a -> b) -> DivAp f b
    }

sus :: (b -> a) -> DivAp f a -> SuspendedDivAp f b a
sus f x = SDA $ \g -> invmap g f x

instance Functor (SuspendedDivAp f b) where
    fmap f (SDA g) = SDA $ \h -> g (h . f)

instance Applicative (SuspendedDivAp f b) where
    pure x = SDA $ \h -> invmap h (const x) (Knot x)    -- hmm...
    SDA f <*> SDA g = SDA $ \h ->
        _ (f (\q -> _)) (g _)

-- Foo Int Bool String
-- Foo <$> mkInt
--     :: f (Bool -> String -> Foo)

-- but can we go from (Bool -> String -> Foo) back to Int?
-- i guess we really cannot? but then how does the other hting work?
--
-- Foo <$> (injectPre fInt mkInt :: f Foo Int)
--      :: f Foo (Bool -> String -> Foo)
--
--      we have no way of getting from (Bool -> String -> Foo) back to Int
--      but it works still because we never directly need it
--      the only way would be to never get to B->S->F as a type parameter,
--      which is what the invariant method uses
--
-- ok, so how important is this?
-- well, we need to use the full invariant mode to implement the "nullable
-- union" thing, to actually manipulate the Dec.  we could, say, remove
-- a type from a union.
--
-- but also i wonder if we could just do something like the listy method?
-- maybe like how we did for splitAp?  hm... yeah that's probably why
-- i couldn't write splitAp directly!  I had to resort to using a list and
-- re-collect instead.  maybe we can do the same thing here.
--

-- apToDivAp :: Ap (Pre a (DivAp f)) a -> DivAp f a
-- apToDivAp = \case
--     Pure r -> Knot r
--     Ap (f :>$<: x) xs -> gather _ _ x (apToDivAp (_ <$> xs))
--     -- Pure r -> Knot r
--     -- Ap x xs -> gather _ (flip ($)) x (apToDivAp xs)


decAltPost :: DecAlt f a -> PostT Dec f a
decAltPost = \case
    Reject h -> PostT $ Lose h
    Swerve f g h x xs -> PostT $
        decide f
          (injectPost g x)
          (hmap (mapPost h) . unPostT $ decAltPost xs)

bypassDecPost :: Dec (Post b f) a -> a -> b
bypassDecPost = \case
    Lose h -> absurd . h
    Choose f (g :<$>: _) xs -> \y -> case f y of
      Left  q -> g q
      Right r -> bypassDecPost xs r

-- ah ok i see now the issue. to fully convert, you have to be able to
-- "piecise-deconstruct" the post-mapping function from stage to stage.
-- but in the PostT Dec version, you only have the full post-mapping, you
-- lose the intermediate stages
-- decNight :: PostT Dec1 f a -> I.Night f (PostT Dec f) a
-- decNight xs0@(PostT (Dec1 f (g :<$>: x) xs)) =
--    Night x (PostT (hmap (mapPost _) xs)) f g (bypassDecPost xs)
-- bypassDecPost' :: Dec (Post b f) a -> b -> a
-- bypassDecPost' = \case
--     Lose h -> _
--     -- Choose f (g :<$>: x) xs -> \y -> case f y of
--     --   Left  q -> g q
--     --   Right r -> bypassDecPost xs r


-- -- so this is the main probleM: Post Dec and Dec Alt are not the same :O
-- -- Post Dec is bigger than DecAlt!
-- postDecAlt :: (b -> a) -> Dec (Post b f) a -> DecAlt f a
-- postDecAlt q = \case
--     Lose h -> Reject h
--     Choose f (g :<$>: x) xs -> Swerve
--       f
--       (q . g)
--       (q . bypassDecPost xs)
--       x
--       (postDecAlt (_ . q) xs)

-- -- so this is the main probleM: Post Dec and Dec Alt are not the same :O
-- -- Post Dec is bigger than DecAlt!
-- postDecAlt :: Dec (Post b f) a -> DecAlt f a
-- postDecAlt xs0 = case xs0 of
--     Lose h -> Reject h
--     Choose f (g :<$>: x) xs -> Swerve
--       (fmap (bypassDecPost xs) . f)
--       _
--       _
--       -- (q . g)
--       -- q
--       x
--       (postDecAlt xs)
--   where
--     q = bypassDecPost xs0
--       -- (postDecAlt (PostT (hmap _ xs)))

-- removeNull :: forall p a. DecAlt1 (TSType_ p) a -> Maybe (ILan Maybe (TSType p 'NotObj) a)
-- removeNull (DecAlt1 f0 g0 h0 x0 xs0) = go f0 g0 h0 x0 xs0
--   where
--     go  :: (r -> Either b c)
--         -> (b -> r)
--         -> (c -> r)
--         -> TSType_ p b
--         -> DecAlt (TSType_ p) c
--         -> Maybe (ILan Maybe (TSType p 'NotObj) r)
--     go f g h (TSType_ x) xs = case x of
--       TSBaseType (ICoyoneda r s TSNull) -> Just
--         . ILan (maybe (g (s ())) h) (either (const Nothing) Just . f)
--         $ case xs of
--             Reject q -> TSBaseType (ICoyoneda q absurd TSNever)
--             Swerve f' g' h' (TSType_ x') xs' -> TSUnion $ PostT $
--               Dec1 f' (g' :<$>: TSType_ x') (hmap (mapPost h') (unPostT (decAltPost xs')))
--       _ -> case xs of
--         Reject _ -> Nothing
--         Swerve f' g' h' (TSType_ x') xs' ->
--           (go f' g' h' (TSType_ x') xs') <&> \(ILan q r t) ->
--             ILan _ _ _
--           -- Nothing -> Nothing
--           -- Just (ILan q r t) -> _

          -- ILan (maybe (g (s ())) absurd) (either (const Nothing) (Just . q) . f) (TSBaseType (inject TSNever))
        -- Swerve f' g' h' (TSType_ xs)
          -- ILan (maybe (g (s ())) absurd) (const Nothing) (TSBaseType (inject TSNever))
      -- Swerve f' g' h' (TSType_ x') xs ->
      --   case x of
      --     TSBaseType (ICoyoneda r s TSNull) -> Just $
      --       ILan (maybe (g (s ())) absurd) (const Nothing) (TSBaseType (inject TSNever))
      -- case go f' g' h' (TSType_ x') xs of
         
-- removeNull :: PostT Dec1 (TSType_ p) a -> Maybe (ILan Maybe (TSType p 'NotObj) a)
-- removeNull (PostT (Dec1 f0 x0 xs0)) = go f0 id x0 xs0
--   where
--     go  :: (b -> Either c d)
--         -> (e -> b)
--         -> Post b (TSType_ p) c
--         -> Dec (Post e (TSType_ p)) d
--         -> Maybe (ILan Maybe (TSType p 'NotObj) b)
--     go f qb (g :<$>: TSType_ x) = \case
--       Lose h -> case x of
--         TSBaseType (ICoyoneda _ r TSNull) -> Just $ ILan (maybe (g (r ())) absurd) (const Nothing) (TSBaseType (inject TSNever))
--         _ -> Nothing
--       Choose f' (g' :<$>: TSType_ x') xs ->
--         case go (_ . f . qb) _ (g' :<$>: TSType_ x') (hmap (mapPost qb) xs) of

-- nullableUnion :: forall p a. PostT Dec1 (TSType_ p) a -> Maybe (ILan Maybe (TSType p 'NotObj) a)
-- nullableUnion (PostT (Dec1 f0 x0 xs0)) = go f0 x0 xs0
--   where
--     go  :: (b -> Either c d)
--         -> Post b (TSType_ p) c
--         -> Dec (Post b (TSType_ p)) d
--         -> Maybe (ILan Maybe (TSType p 'NotObj) b)
--     go f (g :<$>: TSType_ x) = \case

-- nullableUnion :: forall p a. PostT Dec1 (TSType_ p) a -> Maybe (ILan Maybe (TSType p 'NotObj) a)
-- nullableUnion (PostT (Dec1 f0 x0 xs0)) = go f0 x0 xs0
--   where
--     go  :: (b -> Either c d)
--         -> Post b (TSType_ p) c
--         -> Dec (Post b (TSType_ p)) d
--         -> Maybe (ILan Maybe (TSType p 'NotObj) b)
--     go f (g :<$>: TSType_ x) = \case
--       Lose h -> invmap g (either id (absurd . h) . f)  <$> isNullable x
--       Choose f' (g' :<$>: x') xs -> case isNullable x of
--       --   -- gotta look further
--         Nothing -> case go (either _ f' . f) (g' :<$>: x') xs of
--         -- (either _ f' . f) (g' :<$>: x') (hmap (mapPost _) $ invmap _ _ xs) of
--         -- Just _ -> undefined
--         -- we can stop here
--         -- Just (ILan h i y) -> Just . invmap _ _ $
--         --   ILan _ _ . TSUnion . PostT $
--         --     decide _
--         --     -- decide (either (_ . i) Right . f)
--         --     -- decide (either (_ . i) (_ . f') . f . g)
--         --       (injectPost _ (TSType_ (invmap _ _ y)))
--         --       -- (injectPost (g . h . Just) (TSType_ y))
--         --       (invmap _ _ $ hmap (mapPost f) $ Dec1 f' (g' :<$>: x') xs)

    -- xs = case isNullable x of
    --   Nothing -> undefined -- gotta look further
    --   -- we can stop here
    --   Just (ILan h i y)  -> case

      -- Just $
      --   ILan _ _ . TSUnion . PostT $
      --     decide _
      --       (injectPost _ (TSType_ y))
      --       (_ xs)




-- | x | null.
isNullable :: TSType p k a -> Maybe (ILan Maybe (TSType p 'NotObj) a)
isNullable = \case
    TSArray _ -> Nothing
    TSTuple _ -> Nothing
    TSObject _ -> Nothing
    TSSingle t -> isNullable t
    TSUnion ts -> undefined
    TSNamedType (TSNamed _ tsn :$ ps) -> case tsn of
      TSNFunc tf    -> isNullable (tsApply tf ps)
      TSNPrimType _ -> Nothing
    TSIntersection _ -> Nothing
    TSVar _ -> Nothing
    TSPrimType _ -> Nothing
    TSBaseType (ICoyoneda _ g p) -> case p of
      TSNull -> Just $ ILan (maybe (g ()) absurd) (const Nothing) (TSBaseType (inject TSNever))
      _      -> Nothing
    -- TSPrimType (PS p f g) -> case p of
    --   -- oh man that Either in the PS is really hampring this huh
    --   TSNull -> Just . invmap _ _ $ ILan _ _ (TSPrimType (PS TSNull Right id))

-- -- | converts a Nullable x to x | null
-- unNullable :: ILan Maybe (TSType p k) a -> TSType p 'NotObj a
-- unNullable (ILan f g t) = TSUnion $ PostT $
--     Dec1 (maybe (Right ()) Left . g) (f . Just :<$>: TSType_ t) $
--       injectPost (\_ -> f Nothing) $ TSType_ (TSPrimType (inject TSNull))


