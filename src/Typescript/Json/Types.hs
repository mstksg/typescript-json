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
  , Mutability(..)
  , TSTransform(..)
  , TSStringManip(..)
  , ExtendsString(..)
  , extendsString
  , applyTransform
  , TSKeyVal
  , TSUnionBranches
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
  , isObjKeys
  , mkNullable
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
  , isNullable
  , flattenUnion
  ) where

import           Control.Applicative.Free
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Fin                          (Fin(..))
import           Data.Functor
import           Data.Functor.Apply
import           Data.Functor.Apply.Free
import           Data.Functor.Combinator
import           Data.Functor.Invariant
import           Data.Functor.Invariant.DecAlt
import           Data.GADT.Show
import           Data.HFunctor.Chain
import           Data.HFunctor.Route
import           Data.Kind
import           Data.List.NonEmpty                (NonEmpty)
import           Data.Map                          (Map)
import           Data.Maybe
import           Data.Scientific                   (Scientific)
import           Data.Set                          (Set)
import           Data.Some                         (Some(..))
import           Data.Text                         (Text)
import           Data.Type.Equality
import           Data.Type.Nat
import           Data.Vec.Lazy                     (Vec(..))
import           Data.Void
import           GHC.Generics                      (Generic)
import           Typescript.Json.Types.Combinators
import           Typescript.Json.Types.SNat
import qualified Control.Applicative.Lift          as Lift
import qualified Data.Aeson                        as A
import qualified Data.Map                          as M
import qualified Data.Text                         as T
import qualified Prettyprinter                     as PP

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

data Mutability = Mutable | ReadOnly
  deriving (Show, Eq, Ord, Generic, Enum, Bounded)

data ObjMember f a = ObjMember
    { objMemberReadOnly :: Mutability
    , objMemberKey :: Text
    , objMemberVal :: (f :+: ILan Maybe f) a
    }

instance HFunctor ObjMember where
    hmap f (ObjMember ro k v) = ObjMember ro k (hbimap f (hmap f) v)

instance HTraversable ObjMember where
    htraverse f (ObjMember ro k v) = ObjMember ro k <$>
      case v of
        L1 x -> L1 <$> f x
        R1 y -> R1 <$> htraverse f y

instance Invariant f => Invariant (ObjMember f) where
    invmap f g (ObjMember ro x y) = ObjMember ro x (invmap f g y)

data IsObjType = NotObj | IsObj

data SIsObjType :: IsObjType -> Type where
    SNotObj :: SIsObjType 'NotObj
    SIsObj  :: SIsObjType 'IsObj

type TSKeyVal p = PreT Ap (ObjMember (TSType_ p))
type TSUnionBranches p = DecAlt1 (TSType_ p)

data TSStringManip = TSUppercase
                   | TSLowercase
                   | TSCapitalize
                   | TSUncapitalize

newtype ExtendsString = ExtendsString { getExtendsString :: Text }

-- | Canonical type to test against when using TSStringManipType
extendsString :: TSType p 'NotObj ExtendsString
extendsString = invmap ExtendsString getExtendsString $ TSPrimType (inject TSString)

-- | Built-in named type transformers in typescript, that should be
-- displayed as such when printed.
data TSTransform :: Nat -> IsObjType -> Type -> Type where
    TSPartial
        :: TSType p 'IsObj a
        -> TSTransform p 'IsObj (Maybe a)
    TSReadOnly
        :: TSType p 'IsObj a
        -> TSTransform p 'IsObj a
    TSStringManipType
        :: TSStringManip
        -> TSType p 'NotObj a
        -> Assign a ExtendsString
        -> TSTransform p 'NotObj a

data TSType :: Nat -> IsObjType -> Type -> Type where
    TSArray        :: ILan [] (TSType p k) a -> TSType p 'NotObj a
    TSTuple        :: PreT Ap (TSType_ p) a -> TSType p 'NotObj a
    TSObject       :: TSKeyVal p a -> TSType p 'IsObj a
    TSSingle       :: TSType p 'IsObj a -> TSType p 'NotObj a
    TSUnion        :: TSUnionBranches p a -> TSType p 'NotObj a
    TSNamedType    :: TSApplied p k a -> TSType p k a
    TSVar          :: !(Fin p) -> TSType p 'NotObj a   -- is NotObj right?
    TSIntersection :: PreT Ap1 (TSType p 'IsObj) a -> TSType p 'IsObj a
    TSTransformType  :: ICoyoneda (TSTransform p k) a -> TSType p k a
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
      TSTransformType _ -> undefined
      TSPrimType p -> TSPrimType (invmap f g p)
      TSBaseType p -> TSBaseType (invmap f g p)

data ParseErr = PEInvalidEnum    [(Text, EnumLit)]
              | PEInvalidString  Text       Text
              | PEInvalidNumber  Scientific Scientific
              | PEInvalidBigInt  Integer    Integer
              | PEPrimitive      (Some TSPrim) Text
              | PENamedPrimitive Text (Some TSNamedPrim) Text
              | PEExtraTuple     Int        Int
              | PENotInUnion     (NonEmpty (PP.Doc ()))
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
    => (Mutability -> Text -> f ~> g)
    -> (forall x. Mutability -> Text -> f x -> g (Maybe x))
    -> ObjMember f ~> g
interpretObjMember f g (ObjMember ro k v) = case v of
    L1 x -> f ro k x
    R1 y -> interpretILan (g ro k) y

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

data TempArg n a b = TempArg (Fin n) (MP (Assign a) b)

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
    TSTransformType _ -> undefined

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
      TSTransformType tf -> TSTransformType (hmap (shiftTransform n) tf)
      TSPrimType t -> TSPrimType t
      TSBaseType t -> TSBaseType t

shiftApplied :: SNat_ r -> TSApplied p k a -> TSApplied (Plus r p) k a
shiftApplied n (TSNamed nm nt :$ xs) =
        TSNamed nm (shiftNameable n nt)
     :$ hmap2 (withArg_ (Arg_ . shiftArg n)) xs

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

shiftTransform :: SNat_ r -> TSTransform p k a -> TSTransform (Plus r p) k a
shiftTransform n = \case
    TSPartial t -> TSPartial (tsShift n t)
    TSReadOnly t -> TSReadOnly (tsShift n t)
    TSStringManipType sm t a -> TSStringManipType sm (tsShift n t) a

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
    TSTransformType (ICoyoneda _ _ tf) -> case tf of
      TSPartial _ -> SIsObj
      TSReadOnly _ -> SIsObj
      TSStringManipType _ _ _ -> SNotObj
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
            q :>$<: TSType_ (invmap f g (mkNullable w))
      )

isObjKeys :: TSType p 'IsObj a -> Set Text
isObjKeys = M.keysSet . splitKeyVal . collapseIsObj

mkNullable :: TSType p k a -> TSType p 'NotObj (Maybe a)
mkNullable t = TSUnion $
     swerve1 (maybe (Right ()) Left) Just (const Nothing)
        (inject (TSType_ t))
        (inject (TSType_ (TSBaseType (inject TSNull))))

-- | Transforms are just deferred evaluations of functions.  here they are
-- actually applied
applyTransform :: TSTransform p k a -> TSType p k a
applyTransform = \case
    TSPartial x -> TSObject . PreT . objectPartial . unPreT $ collapseIsObj x
    TSReadOnly x -> TSObject . hmap (\o -> o { objMemberReadOnly = ReadOnly }) $ collapseIsObj x
    TSStringManipType mf t _ -> mapStringLit (stringManipFunc mf) t

stringManipFunc :: TSStringManip -> Text -> Text
stringManipFunc = \case
    TSUppercase -> T.toUpper
    TSLowercase -> T.toLower
    TSCapitalize -> uncurry (<>) . first T.toUpper . T.splitAt 1
    TSUncapitalize -> uncurry (<>) . first T.toLower . T.splitAt 1

-- | Pulls out the (x | y | z) from (x | y | z) | null.  The result is an
-- 'ILan' where the item inside is non-nullable.
--
-- This removes ALL nulls and undefineds.
--
-- Note that, if the result is Just (it is nullable), this inlines all
-- named times because it changes the structure of the type itself.
isNullable :: TSType p k a -> Maybe (ILan Maybe (TSType p 'NotObj) a)
isNullable = \case
    TSArray _ -> Nothing
    TSTuple _ -> Nothing
    TSObject _ -> Nothing
    TSSingle t -> isNullable t
    TSUnion ts -> nullableUnion ts
    TSNamedType (TSNamed _ tsn :$ ps) -> case tsn of
      TSNFunc tf    -> isNullable (tsApply tf ps)
      TSNPrimType _ -> Nothing
    TSIntersection _ -> Nothing
    TSVar _ -> Nothing
    TSTransformType tf -> isNullable $ interpret applyTransform tf
    TSPrimType _ -> Nothing
    TSBaseType (ICoyoneda _ g p) -> case p of
      TSNull      -> Just $ ILan (maybe (g ()) absurd) (const Nothing) (TSBaseType (inject TSNever))
      TSUndefined -> Just $ ILan (maybe (g ()) absurd) (const Nothing) (TSBaseType (inject TSNever))
      _      -> Nothing

-- | Remove all nullable types from a union.  Used in 'isNullable'.
nullableUnion :: forall p a. DecAlt1 (TSType_ p) a -> Maybe (ILan Maybe (TSType p 'NotObj) a)
nullableUnion (DecAlt1 f0 ga0 gb0 x0 xs0) = go f0 ga0 gb0 x0 xs0
  where
    go  :: (r -> Either b c)
        -> (b -> r)
        -> (c -> r)
        -> TSType_ p b
        -> DecAlt (TSType_ p) c
        -> Maybe (ILan Maybe (TSType p 'NotObj) r)
    go f ga gb (TSType_ x) xs = case isNullable x of
      -- not here
      Nothing -> case xs of
        -- ... not nowhere
        Reject _ -> Nothing
        -- ... but there
        Swerve f' ga' gb' x' xs' ->
          -- in: f, r
          -- out: ga, gb, q
          go f' ga' gb' x' xs' <&> \(ILan q r ys) ->
            ILan (either ga (gb . q) . sequence) (traverse r . f) $ TSUnion $
              swerved1
                (inject (TSType_ x))
                (inject (TSType_ ys))
      -- it's here! might as well remove all the rest as well
      Just (ILan q r y) -> Just $ case xs of
        -- remove all others
        Reject h -> ILan (ga . q) (either r (absurd . h) . f) y
        Swerve f' ga' gb' x' xs' -> case go f' ga' gb' x' xs' of
          -- the rest were not nullable
          Nothing ->
            case y of
              -- if y is never then we can just delete it from the union
              TSBaseType (ICoyoneda s _ TSNever) ->
                -- in: f, r, s
                -- out: ga, gb, q, t
                ILan (maybe (ga (q Nothing)) gb)
                     (fmap (either absurd id) . bitraverse (fmap s . r) pure . f) $
                    TSUnion $ DecAlt1 f' ga' gb' x' xs'
              _ -> ILan (maybe (ga (q Nothing)) (either (ga . q . Just) gb)) (bitraverse r pure . f) $ TSUnion $
                DecAlt1 id Left Right (TSType_ y) xs
          -- the rest had nullable stuff too
          Just (ILan q' r' ys) ->
            case y of
              -- if y is never then we can just delete it from the union
              TSBaseType (ICoyoneda s _ TSNever) ->
                ILan (gb . q')
                     (fmap (either (absurd . s) id) . bitraverse r r' . f)
                     ys
              _ ->
                -- we have an option of using 'q Nothing' of 'q1 Nothing',
                -- because there are multiple nulls removed.  this
                -- basically determines where we route the Nothing input
                -- TODO: check to make sure the same Nothing is routed in
                -- both encoding and decoding
                ILan (maybe (ga (q Nothing)) (either (ga . q . Just) (gb . q' . Just)))
                    ((bitraverse r pure =<<)  . traverse r' . f) $ TSUnion $
                  swerved1
                    (inject (TSType_ y))
                    (inject (TSType_ ys))

flattenUnion :: TSType p k a -> Maybe (DecAlt1 (TSType_ p) a)
flattenUnion = \case
    TSArray _ -> Nothing
    TSTuple _ -> Nothing
    TSObject _ -> Nothing
    -- TODO: this HMonad instance should be a thing already?
    TSUnion xs -> Just
                . foldChain1 id (\(Night x y f ga gb) -> swerve1 f ga gb x y)
                . unDecAlt1
                . hmap (\(TSType_ t) -> fromMaybe (inject (TSType_ t)) (flattenUnion t))
                $ xs
    TSSingle x -> flattenUnion x
    TSNamedType (TSNamed _ tsn :$ ps) -> case tsn of
      TSNFunc tf    -> flattenUnion (tsApply tf ps)
      TSNPrimType _ -> Nothing
    TSVar _ -> Nothing
    TSIntersection _ -> Nothing
    TSTransformType _ -> undefined
    TSPrimType _ -> Nothing
    TSBaseType _ -> Nothing

objectPartial
    :: Ap (Pre b (ObjMember (TSType_ p))) a
    -> Ap (Pre (Maybe b) (ObjMember (TSType_ p))) (Maybe a)
objectPartial = \case
    Pure x -> Pure (Just x)
    Ap (f :>$<: o@ObjMember{..}) xs ->
      Ap (fmap f :>$<: (
            o { objMemberVal = R1 $ case objMemberVal of
                  L1 x -> ilan x
                  R1 (ILan q r y) -> ILan (Just . q) (r =<<) y
              }
           )
         )
         ((=<<) . sequenceA <$> objectPartial xs)

mapStringLit
    :: forall p k a. ()
    => (Text -> Text)
    -> TSType p k a
    -> TSType p k a
mapStringLit f = go
  where
    go :: TSType q j b -> TSType q j b
    go t0 = case t0 of
      TSArray _ -> t0
      TSTuple _ -> t0
      TSObject _ -> t0
      TSUnion xs -> TSUnion $ hmap (mapTSType_ go) xs
      TSSingle x -> TSSingle (go x)
      TSNamedType (TSNamed _ tsn :$ ps) -> case tsn of
        TSNFunc tf    -> go (tsApply tf ps)
        TSNPrimType _ -> t0
      TSVar _ -> t0
      TSIntersection _ -> t0
      TSTransformType tf -> go $ interpret applyTransform tf
      TSPrimType PS{..} -> case psItem of
        TSStringLit s -> TSPrimType $ PS { psItem = TSStringLit (f s), .. }
        _             -> t0
      TSBaseType _ -> t0
