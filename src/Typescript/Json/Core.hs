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

module Typescript.Json.Core (
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
  , IsInterface(..)
  , mapName
  , onTSType_
  , decideTSType_
  , mapTSType_
  , withTSType_
  , IsObjType(..)
  , SIsObjType(..)
  , tsObjType
  , tsShift
  , SNat_(..)
  -- * Generics
  , TSTypeF(..)
  , TSTypeF_(..)
  , mapTSTypeF_
  , withTSTypeF_
  , tsApply
  , tsApply1
  , tsApplyVar
  , tsApplyVar1
  -- , compGeneric
  -- * prettyprint
  , ppEnumLit
  , ppPrim
  , ppType'
  , ppType
  , ppTypeWith
  , ppTypeF'
  , ppTypeF
  , ppTypeFWith
  , typeExports'
  , typeExports
  , typeExports_
  , namedTypeExports'
  , namedTypeExports
  -- * to value
  , enumLitToValue
  , primToValue
  , typeToValue
  , encodeEnumLit
  , primToEncoding
  , typeToEncoding
  -- * parse
  , parseEnumLit
  , parsePrim
  , parseType
  , ParseErr(..)
  -- * utility func
  , interpretObjMember
  ) where

import           Control.Applicative
import           Control.Applicative.Free
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Fin                                  (Fin(..))
import           Data.Foldable
import           Data.Functor
import           Data.Ord
import           Data.Functor.Combinator hiding            (Comp(..))
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divisible.Free (Dec(..))
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.GADT.Show
import           Data.HFunctor.Route
import           Data.Kind
import           Data.Map                                  (Map)
import           Data.Maybe
import           Data.SOP                                  (NP(..), K(..))
import           Data.Scientific                           (Scientific, toBoundedInteger)
import           Data.Set                                  (Set)
import           Data.Some                                 (Some(..))
import           Data.Text                                 (Text)
import           Data.Type.Equality
import           Data.Type.Nat
import           Data.Vec.Lazy                             (Vec)
import           Data.Void
import           Typescript.Json.Core.Combinators
import qualified Data.Aeson                                as A
import qualified Data.Aeson.BetterErrors                   as ABE
import qualified Data.Aeson.Encoding                       as AE
import qualified Data.Aeson.Types                          as A
import qualified Data.Graph.Inductive.Graph                as FGL
import qualified Data.Graph.Inductive.PatriciaTree         as FGL
import qualified Data.Graph.Inductive.Query.DFS            as FGL
import qualified Data.Map                                  as M
import qualified Data.SOP                                  as SOP
import qualified Data.Set                                  as S
import qualified Data.Text                                 as T
import qualified Data.Type.Nat                             as Nat
import qualified Data.Vec.Lazy                             as Vec
import qualified Data.Vector                               as V
import qualified Prettyprinter                             as PP

data EnumLit = ELString Text | ELNumber Scientific
  deriving (Show, Eq, Ord)

data TSPrim :: Type -> Type where
    TSBoolean    :: TSPrim Bool
    TSNumber     :: TSPrim Scientific
    TSBigInt     :: TSPrim Integer
    TSString     :: TSPrim Text
    -- TSEnum       :: Text -> Vec n (Text, EnumLit) -> TSPrim (Fin n)
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

data TSType_ p n a = forall k. TSType_ { unTSType_ :: TSType p k n a }

instance Invariant (TSType_ p n) where
    invmap f g = mapTSType_ (invmap f g)

withTSType_
    :: (forall k. TSType p k n a -> r)
    -> TSType_ p n a
    -> r
withTSType_ f (TSType_ t) = f t

mapTSType_
    :: (forall k. TSType p k n a -> TSType us k m b)
    -> TSType_ p n a
    -> TSType_ us m b
mapTSType_ f = withTSType_ (TSType_ . f)

-- traverseTSType_
--     :: Functor f
--     => (forall k. TSType p k n a -> f (TSType p k m b))
--     -> TSType_ p n a
--     -> f (TSType_ p m b)
-- traverseTSType_ f (TSType_ t) = TSType_ <$> f t

data IsInterface n = NotInterface | IsInterface n
  deriving (Show, Eq, Ord, Functor)

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

interpretObjMember
    :: Invariant g
    => (Text -> f ~> g)
    -> (forall x. Text -> f x -> g (Maybe x))
    -> ObjMember f ~> g
interpretObjMember f g (ObjMember k v) = case v of
    L1 x -> f k x
    R1 y -> interpretILan (g k) y

instance Invariant f => Invariant (ObjMember f) where
    invmap f g (ObjMember x y) = ObjMember x (invmap f g y)

data IsObjType = NotObj | IsObj

data SIsObjType :: IsObjType -> Type where
    SNotObj :: SIsObjType 'NotObj
    SIsObj  :: SIsObjType 'IsObj

type TSKeyVal p n = PreT Ap (ObjMember (TSType_ p n))

data TSType :: Nat -> IsObjType -> Type -> Type -> Type where
    TSArray        :: ILan [] (TSType p k n) a -> TSType p 'NotObj n a
    TSNullable     :: ILan Maybe (TSType p k n) a -> TSType p 'NotObj n a
    TSTuple        :: PreT Ap (TSType_ p n) a -> TSType p 'NotObj n a
    TSObject       :: TSKeyVal p n a -> TSType p 'IsObj n a
    TSSingle       :: TSType p 'IsObj n a -> TSType p 'NotObj n a
    TSUnion        :: PostT Dec (TSType_ p n) a -> TSType p 'NotObj n a
    TSNamedType    :: TSNamed p k n as a -> NP (TSType_ p n) as -> TSType p k n a
    TSVar          :: !(Fin p) -> TSType p 'NotObj n a   -- is NotObj right?
    TSIntersection :: PreT Ap (TSType p 'IsObj n) a -> TSType p 'IsObj n a
    TSExternal     :: SIsObjType k -> !n -> [Text] -> TSType p k n a
    TSPrimType     :: PS TSPrim a -> TSType p 'NotObj n a

data TSNameable :: Nat -> IsObjType -> Type -> [Type] -> Type -> Type where
    TSNFunc     :: TSTypeF p k n as a -> TSNameable p k n as a
    TSNPrimType :: PS TSNamedPrim a -> TSNameable p 'NotObj n '[] a

instance Invariant (TSNameable p k n as) where
    invmap f g = \case
      TSNFunc x     -> TSNFunc (invmap f g x)
      TSNPrimType x -> TSNPrimType (invmap f g x)

data TSNamed_ p n as a = forall k. TSNamed_ (TSNamed p k n as a)

withTSNamed_
    :: (forall k. TSNamed p k n as a -> r)
    -> TSNamed_ p n as a
    -> r
withTSNamed_ f (TSNamed_ t) = f t

data TSNamed p k n as a = TSNamed
    { tsnName :: Text
    , tsnType :: TSNameable p k n as a
    }

instance Invariant (TSNamed p k n as) where
    invmap f g (TSNamed n t) = TSNamed n (invmap f g t)

instance Invariant (TSNamed_ p n as) where
    invmap f g (TSNamed_ x) = TSNamed_ (invmap f g x)

-- TODO: new idea...no need for n type variable if we always just directly
-- encode into text on-the-fly?  so flatten returns docs directly instead
-- of types.  then we don't need External either
--
-- yeah, external really only lives inside the library, and there's no
-- reason to actually expose it to the user.
--
-- hm...unless maybe the user specifically wants to make it external
--
-- maybe there could be a "custom" that just lets us parse/make a json.
-- a Prim with a name, that could just contain the PS serialization
-- directly for when we actually need to encode/decode
--
-- then we don't ever need any externals as a part of the API

data TSTypeF :: Nat -> IsObjType -> Type -> [Type] -> Type -> Type where
    TSGeneric
        :: NP (K Text) as
        -> (forall r. SNat_ r -> NP (TSType_ (Plus r p) n) as -> TSType (Plus r p) k n b)
        -> TSTypeF p k n as b
    TSGenericInterface
        :: NP (K Text) as
        -> (forall r. SNat_ r -> NP (TSType_ (Plus r p) n) as -> TSKeyVal (Plus r p) n b)
        -> TSTypeF p 'IsObj n as b

instance Invariant (TSTypeF p k n as) where
    invmap f g (TSGeneric xs h) =
        TSGeneric xs (\q -> invmap f g . h q)
    invmap f g (TSGenericInterface xs h) =
        TSGenericInterface xs (\q -> invmap f g . h q)

data TSTypeF_ p n as b = forall k. TSTypeF_ { unTSTypeF_ :: TSTypeF p k n as b }

instance Invariant (TSTypeF_ p n as) where
    invmap f g (TSTypeF_ x) = TSTypeF_ (invmap f g x)

instance Invariant (TSType p k n) where
    invmap f g = \case
      TSArray  t  -> TSArray (invmap f g t )
      TSNullable t -> TSNullable (invmap f g t)
      TSTuple  ts -> TSTuple (invmap f g ts)
      TSObject ts -> TSObject (invmap f g ts)
      TSSingle ts -> TSSingle (invmap f g ts)
      TSUnion  ts -> TSUnion (invmap f g ts)
      TSNamedType (TSNamed nm nt) xs -> case nt of
        TSNFunc tf -> TSNamedType (TSNamed nm (TSNFunc (invmap f g tf))) xs
        TSNPrimType ps -> TSNamedType (TSNamed nm (TSNPrimType (invmap f g ps))) xs
      TSVar i -> TSVar i
      TSIntersection ts -> TSIntersection (invmap f g ts)
      TSExternal o e ps -> TSExternal o e ps
      TSPrimType p -> TSPrimType (invmap f g p)

withTSTypeF_
    :: (forall k. TSTypeF p k n as b -> r)
    -> TSTypeF_ p n as  b
    -> r
withTSTypeF_ f (TSTypeF_ x) = f x

mapTSTypeF_
    :: (forall k. TSTypeF p k n as b -> TSTypeF q k m as' b')
    -> TSTypeF_ p n as  b
    -> TSTypeF_ q m as' b'
mapTSTypeF_ f = withTSTypeF_ (TSTypeF_ . f)

tsApply
    :: TSTypeF p k n as b      -- ^ type function
    -> NP (TSType_ p n) as     -- ^ thing to apply
    -> TSType p k n b
tsApply (TSGeneric _ f) t = f SZ_ t
tsApply (TSGenericInterface _ f) t = TSObject (f SZ_ t)
-- tsApply p@(TSPrimTypeF _ _) _ = TSApplied p Nil

tsApply1
    :: TSTypeF p k n '[a] b      -- ^ type function
    -> TSType_ p n a         -- ^ thing to apply
    -> TSType p k n b
tsApply1 (TSGeneric _ f) t = f SZ_ (t :* Nil)
tsApply1 (TSGenericInterface _ f) t = TSObject (f SZ_ (t :* Nil))

withParams
    :: NP (K Text) as
    -> (forall bs. Vec bs Text -> NP (K (Fin bs)) as -> r)
    -> r
withParams = \case
    Nil -> \f -> f Vec.VNil Nil
    K p :* ps -> \f -> withParams ps $ \bs (es :: NP (K (Fin bs)) as) ->
      f (p Vec.::: bs) (K FZ :* hmap (K . FS . SOP.unK) es)

weakenFin
    :: forall as bs. ()
    => Fin as
    -> Fin (Plus as bs)
weakenFin = \case
    FZ   -> FZ
    FS i -> FS (weakenFin @_ @bs i)

tsApplyVar1
    :: forall p k n a b r. ()
    => TSTypeF p k n '[a] b
    -> (TSType ('Nat.S p) k n b -> r)
    -> r
tsApplyVar1 (TSGeneric _ g) f =
    f (g (SS_ SZ_) (TSType_ (TSVar FZ) :* Nil))
tsApplyVar1 (TSGenericInterface _ g) f =
    f (TSObject (g (SS_ SZ_) (TSType_ (TSVar FZ) :* Nil)))

tsApplyVar
    :: forall p k n as b r. ()
    => TSTypeF p k n as b
    -> (forall s. Vec s Text -> TSType (Plus s p) k n b -> r)
    -> r
tsApplyVar (TSGeneric ps g) f = withParams ps $ \rs es ->
     f rs   -- shodowing should happen on the level of withParams?
     -- f (fmap (shadow oldVars) rs)
       (g (vecToSNat_ rs) (hmap (TSType_ . TSVar . weakenFin @_ @p . SOP.unK) es))
  -- where
  --   oldVars :: Set Text
  --   oldVars = S.fromList (htoList SOP.unK ps)
tsApplyVar (TSGenericInterface ps g) f = withParams ps $ \rs es ->
     f rs
       (TSObject (g (vecToSNat_ rs) (hmap (TSType_ . TSVar . weakenFin @_ @p . SOP.unK) es)))
-- tsApplyVar (TSPrimTypeF n p) f = f Vec.VNil (TSApplied (TSPrimTypeF n p) Nil)   -- is this going to be a problem?

-- shadow :: Set Text -> Text -> Text
-- shadow ps t0 = go Nothing
  -- where
  --   go i
  --       | t `S.member` ps = go (Just (maybe 0 (+1) i))
  --       | otherwise       = t
  --     where
  --       t = appendNum i t0
  --   appendNum Nothing  = id
  --   appendNum (Just i) = (<> T.pack (show @Int i))


vecToSNat_ :: forall n b. Vec n b -> SNat_ n
vecToSNat_ = \case
    Vec.VNil     -> SZ_
    _ Vec.::: xs -> SS_ (vecToSNat_ xs)

tsShift
    :: forall r p k n a. ()
    => SNat_ r
    -> TSType p k n a
    -> TSType (Plus r p) k n a
tsShift n = go
  where
    go :: forall q j b. TSType q j n b -> TSType (Plus r q) j n b
    go = \case
      TSArray ts -> TSArray (hmap go ts)
      TSNullable ts -> TSNullable (hmap go ts)
      TSTuple ts -> TSTuple (hmap (mapTSType_ go) ts)
      TSUnion ts -> TSUnion (hmap (mapTSType_ go) ts)
      TSObject ts -> TSObject (hmap (hmap (mapTSType_ go)) ts)
      TSSingle t  -> TSSingle (go t)
      TSNamedType (TSNamed nm nt) xs -> case nt of
        TSNFunc (TSGeneric ps f) -> TSNamedType (TSNamed nm
          (TSNFunc $ TSGeneric ps $ \q ->
             case assocPlus @_ @r @q q of
               Refl -> f (plusNat q n)
          ))
          (hmap (mapTSType_ go) xs)
        TSNFunc (TSGenericInterface ps f) -> TSNamedType (TSNamed nm
          (TSNFunc $ TSGenericInterface ps $ \q ->
             case assocPlus @_ @r @q q of
               Refl -> f (plusNat q n)
          ))
          (hmap (mapTSType_ go) xs)
        TSNPrimType ps -> TSNamedType (TSNamed nm (TSNPrimType ps)) Nil
      TSIntersection t -> TSIntersection (hmap go t)
      TSExternal m t ps -> TSExternal m t ps
      TSVar i    -> TSVar (shiftFin n i)
      TSPrimType t -> TSPrimType t

shiftFin
    :: forall as bs. ()
    => SNat_ as
    -> Fin bs
    -> Fin (Plus as bs)
shiftFin = \case
    SZ_ -> id
    SS_ n -> FS . shiftFin n

plusNat
    :: SNat_ as
    -> SNat_ bs
    -> SNat_ (Plus as bs)
plusNat = \case
    SZ_ -> id
    SS_ n -> SS_ . plusNat n

data SNat_ :: Nat -> Type where
    SZ_ :: SNat_ 'Nat.Z
    SS_ :: SNat_ n -> SNat_ ('Nat.S n)

tsObjType
    :: TSType p k n a
    -> SIsObjType k
tsObjType = \case
    TSArray  _                    -> SNotObj
    TSNullable _                  -> SNotObj
    TSTuple  _                    -> SNotObj
    TSObject _                    -> SIsObj
    TSSingle _                    -> SNotObj
    TSUnion  _                    -> SNotObj
    TSNamedType (TSNamed _ nt) _     -> case nt of
      TSNFunc tsf@(TSGeneric{})      -> tsApplyVar tsf $ \_ -> tsObjType
      TSNFunc (TSGenericInterface{}) -> SIsObj
      TSNPrimType _                  -> SNotObj
    TSVar _                       -> SNotObj
    TSIntersection _              -> SIsObj
    TSExternal o _ _              -> o
    TSPrimType _                  -> SNotObj


onTSType_
    :: (TSType p 'NotObj n a -> r)
    -> (TSType p 'IsObj  n a -> r)
    -> TSType_ p n a
    -> r
onTSType_ f g (TSType_ t) = case tsObjType t of
    SNotObj -> f t
    SIsObj  -> g t

decideTSType_ :: TSType_ p n ~> (TSType p 'NotObj n :+: TSType p 'IsObj n)
decideTSType_ = onTSType_ L1 R1


mapName :: forall p k n m. (m -> n) -> (n -> m) -> TSType p k n ~> TSType p k m
mapName f g = go
  where
    go :: TSType us j n ~> TSType us j m
    go = \case
      TSArray l         -> TSArray (hmap go l)
      TSNullable l      -> TSNullable (hmap go l)
      TSTuple ts        -> TSTuple (hmap (mapTSType_ go) ts)
      TSObject ts       -> TSObject (hmap (hmap (mapTSType_ go)) ts)
      TSSingle ts       -> TSSingle (go ts)
      TSUnion ts        -> TSUnion (hmap (mapTSType_ go) ts)
      TSNamedType (TSNamed nm nt) xs -> case nt of
        TSNFunc (TSGeneric p h) -> TSNamedType
          (TSNamed nm (TSNFunc $ TSGeneric p (\q -> go . h q . hmap (mapTSType_ (mapName g f)))))
          (hmap (mapTSType_ go) xs)
        TSNFunc (TSGenericInterface p h) -> TSNamedType
          (TSNamed nm (TSNFunc $ TSGenericInterface p (\q -> hmap (hmap (mapTSType_ go)) . h q . hmap (mapTSType_ (mapName g f)))))
          (hmap (mapTSType_ go) xs)
        TSNPrimType p -> TSNamedType (TSNamed nm (TSNPrimType p)) Nil
      TSVar i           -> TSVar i
      TSIntersection ts -> TSIntersection (hmap go ts)
      TSExternal o n ps -> TSExternal o (g n) ps
      TSPrimType t      -> TSPrimType t

ppScientific :: Scientific -> PP.Doc x
ppScientific n = maybe (PP.pretty (show n)) PP.pretty
               . toBoundedInteger @Int
               $ n

ppEnumLit :: EnumLit -> PP.Doc x
ppEnumLit = \case
    ELString t -> PP.pretty (show t)
    ELNumber n -> ppScientific n

ppPrim :: TSPrim a -> PP.Doc x
ppPrim = \case
    TSBoolean      -> "boolean"
    TSNumber       -> "number"
    TSBigInt       -> "bigint"
    TSString       -> "string"
    -- TSEnum n es    -> PP.fillSep
    --   [ "enum"
    --   , PP.pretty n
    --   , PP.encloseSep "{" "}" ","
    --       [ PP.pretty e PP.<+> "=" PP.<+> ppEnumLit x
    --       | (e, x) <- toList es
    --       ]
    --   ]
    TSStringLit t  -> PP.pretty (show t)
    TSNumericLit n -> ppScientific n
    TSBigIntLit n  -> PP.pretty n
    TSUnknown      -> "unknown"
    TSAny          -> "any"
    TSVoid         -> "void"
    TSUndefined    -> "undefined"
    TSNull         -> "null"
    TSNever        -> "never"

ppNamedPrim :: Text -> TSNamedPrim a -> PP.Doc x
ppNamedPrim n = \case
    TSEnum es    -> PP.fillSep
      [ "enum"
      , PP.pretty n
      , PP.encloseSep "{" "}" ","
          [ PP.pretty e PP.<+> "=" PP.<+> ppEnumLit x
          | (e, x) <- toList es
          ]
      ]

ppType
    :: TSType_ 'Nat.Z Void a
    -> PP.Doc x
ppType = ppType' Vec.VNil

ppType'
    :: Vec p Text
    -> TSType_ p Void a
    -> PP.Doc x
ppType' ps = withTSType_ (ppTypeWith absurd ps)

ppTypeWith
    :: forall p k n a x. ()
    => (n -> PP.Doc x)
    -> Vec p Text
    -> TSType p k n a
    -> PP.Doc x
ppTypeWith f = go
  where
    go :: Vec q Text -> TSType q j n b -> PP.Doc x
    go ps = \case
      TSArray t   -> getConst (interpretILan (Const . go ps) t) <> "[]"
      TSNullable t -> getConst (interpretILan (Const . go ps) t) PP.<+> "| null"
      TSTuple ts  -> PP.encloseSep "[ " " ]" ", " (htoList (withTSType_ (go ps)) ts)
      TSObject ts -> PP.encloseSep "{ " " }" ", " $
        htoList
          ( getConst . interpretObjMember
              (\k x -> Const (PP.pretty k <> ":"  PP.<+> withTSType_ (go ps) x ))
              (\k x -> Const (PP.pretty k <> "?:" PP.<+> withTSType_ (go ps) x))
          )
          ts
      TSSingle ts -> go ps ts
      TSUnion ts  -> PP.encloseSep "" "" " | " (htoList (withTSType_ (go ps)) ts)
      -- this is the benefit of delaying application
      TSNamedType (TSNamed nm _) xs ->
        let args = htoList (withTSType_ (go ps)) xs
        in  PP.pretty nm <>
              (if null args then ""
                            else PP.encloseSep "<" ">" "," args
              )
      TSVar i -> PP.pretty (ps Vec.! i)
      TSIntersection ts  -> PP.encloseSep "" "" " & " (htoList (go ps) ts)
      TSExternal _ n qs -> f n <>
        if null qs
          then mempty
          else PP.encloseSep "<" ">" "," (PP.pretty <$> qs)
      TSPrimType PS{..} -> ppPrim psItem

ppTypeF
    :: PP.Pretty n
    => Text
    -> TSTypeF_ 'Nat.Z n a b
    -> PP.Doc x
ppTypeF nm = ppTypeF' nm Vec.VNil

ppTypeF'
    :: PP.Pretty n
    => Text
    -> Vec p Text
    -> TSTypeF_ p n a b
    -> PP.Doc x
ppTypeF' n ps = withTSTypeF_ (ppTypeFWith PP.pretty n ps)

-- TODO: figure out shadowing
ppTypeFWith
    :: (n -> PP.Doc x)
    -> Text
    -> Vec p Text
    -> TSTypeF p k n a b
    -> PP.Doc x
ppTypeFWith f n ps tf@(TSGeneric vs _) = PP.hsep [
      "type"
        PP.<+> PP.pretty n
        PP.<> (if null args then ""
                            else PP.encloseSep "<" ">" "," args
              )
    , "="
    , tsApplyVar tf $ \rs -> ppTypeWith f (rs Vec.++ ps)
    ]
  where
    args = htoList (PP.pretty . SOP.unK) vs
ppTypeFWith f n ps tf@(TSGenericInterface vs _) = PP.hsep [
      "interface"
        PP.<> PP.pretty n
        PP.<> (if null args then ""
                            else PP.encloseSep "<" ">" "," args
              )
    , "="
    , tsApplyVar tf $ \rs -> ppTypeWith f (rs Vec.++ ps)
    ]
  where
    args = htoList (PP.pretty . SOP.unK) vs

typeExports_
    :: TSType_ 'Nat.Z Void a
    -> PP.Doc x
typeExports_ = withTSType_ typeExports

typeExports
    :: TSType 'Nat.Z k Void a
    -> PP.Doc x
typeExports = typeExports' Vec.VNil

typeExports'
    :: Vec p Text
    -> TSType p k Void a
    -> PP.Doc x
typeExports' ps = ppMap . flattenType ps

namedTypeExports
    :: TSNamed 'Nat.Z k Void as a
    -> PP.Doc x
namedTypeExports = namedTypeExports' Vec.VNil

namedTypeExports'
    :: Vec p Text
    -> TSNamed p k Void as a
    -> PP.Doc x
namedTypeExports' ps = ppMap . flattenNamedType ps

ppMap
    :: forall x. ()
    => Map Text (Set Text, PP.Doc x)
    -> PP.Doc x
ppMap (M.mapKeys Down->mp) = PP.vcat $
    ("export" PP.<+>) <$> FGL.topsort' graph
  where
    nodes = zip [0..] (toList mp)
    graph :: FGL.Gr (PP.Doc x) ()
    graph = FGL.mkGraph
      (second snd <$> nodes)
      [ (i, j, ())
      | (i, (refs, _)) <- nodes
      , r <- S.toList refs
      , j <- maybeToList $ M.lookupIndex (Down r) mp
      ]


-- | Pull out all of the named types to be top-level type declarations, and
-- have create a map of all of those declarations.
flattenNamedType
    :: Vec p Text
    -> TSNamed p k Void as a
    -> Map Text (Set Text, PP.Doc x)
flattenNamedType ps t = execState (flattenNamedType_ ps t) M.empty

-- | Ignores the top level type, so why even bother?
flattenType
    :: Vec p Text
    -> TSType p k Void a
    -> Map Text (Set Text, PP.Doc x)
flattenType ps t = execState (flattenType_ ps t) M.empty

flattenNamedType_
    :: forall p k a as x. ()
    => Vec p Text
    -> TSNamed p k Void as a
    -> State (Map Text (Set Text, PP.Doc x)) (Set Text)
flattenNamedType_ ps TSNamed{..} = case tsnType of
    TSNPrimType PS{..} -> do
      modify $ M.insert tsnName (S.empty, ppNamedPrim tsnName psItem)
      pure S.empty
    TSNFunc tsf -> do
      deps <- tsApplyVar tsf $ \rs t -> flattenType_ (rs Vec.++ ps) t
      modify $ M.insert tsnName $
        (deps, ppTypeFWith PP.pretty tsnName ps tsf)
      pure deps

flattenType_
    :: forall p k a x. ()
    => Vec p Text
    -> TSType p k Void a
    -> State (Map Text (Set Text, PP.Doc x)) (Set Text)
flattenType_ ps = go
  where
    go  :: forall j b. ()
        => TSType p j Void b
        -> State (Map Text (Set Text, PP.Doc x)) (Set Text)
    go = \case
      TSArray ts   -> hfoldMap SOP.unK <$> htraverse (fmap K . go) ts
      TSNullable t -> hfoldMap SOP.unK <$> htraverse (fmap K . go) t
      TSTuple ts   -> hfoldMap SOP.unK <$> htraverse (withTSType_ (fmap K . go)) ts
      TSObject ts  -> hfoldMap (hfoldMap SOP.unK) <$> htraverse (htraverse (withTSType_ (fmap K . go))) ts
      TSSingle t   -> go t
      TSUnion ts   -> hfoldMap SOP.unK <$> htraverse (withTSType_ (fmap K . go)) ts
      TSNamedType tsn args -> do
        deps1 <- hfoldMap SOP.unK <$> htraverse (withTSType_ (fmap K . go)) args
        deps2 <- flattenNamedType_ ps tsn
        pure $ deps1 <> deps2
      TSVar _      -> pure S.empty
      TSIntersection ts -> hfoldMap SOP.unK <$> htraverse (fmap K . go) ts
      TSPrimType _ -> pure S.empty

assocPlus
    :: forall a b c. ()
    => SNat_ a
    -> Plus a (Plus b c) :~: Plus (Plus a b) c
assocPlus = \case
    SZ_ -> Refl
    SS_ n -> case assocPlus @_ @b @c n  of
      Refl -> Refl

encodeEnumLit :: EnumLit -> A.Encoding
encodeEnumLit = \case
    ELString t -> AE.text t
    ELNumber n -> AE.scientific n

primToEncoding :: TSPrim a -> a -> A.Encoding
primToEncoding = \case
    TSBoolean -> AE.bool
    TSNumber  -> AE.scientific
    -- hm...
    TSBigInt  -> AE.integer
    TSString  -> AE.text
    TSStringLit t -> \_ -> AE.text t
    TSNumericLit n -> \_ -> AE.scientific n
    -- hm...
    TSBigIntLit n -> \_ -> AE.integer n
    TSUnknown -> AE.value
    TSAny -> AE.value
    -- hm...
    TSVoid -> \_ -> AE.null_
    TSUndefined -> \_ -> AE.null_
    TSNull -> \_ -> AE.null_
    TSNever -> absurd

namedPrimToEncoding :: TSNamedPrim a -> a -> A.Encoding
namedPrimToEncoding = \case
    TSEnum e -> \i -> encodeEnumLit (snd (e Vec.! i))

objTypeToEncoding :: TSType 'Nat.Z 'IsObj Void a -> Op A.Series a
objTypeToEncoding = \case
    TSObject       ts -> keyValToValue ts
    TSIntersection ts -> preDivisibleT objTypeToEncoding ts
    TSNamedType (TSNamed _ nt) xs -> case nt of
      TSNFunc f -> objTypeToEncoding (tsApply f xs)
  where
    keyValToValue :: TSKeyVal 'Nat.Z Void ~> Op A.Series
    keyValToValue = preDivisibleT
        ( interpretObjMember
            (\k t -> Op           $ \x -> k A..= withTSType_ typeToValue t x)
            (\k t -> Op . foldMap $ \x -> k A..= withTSType_ typeToValue t x)
        )

typeToEncoding :: TSType 'Nat.Z k Void a -> a -> A.Encoding
typeToEncoding = \case
    TSArray ts        -> AE.list id
                       . getOp (interpretILan (\t -> Op ( map (typeToEncoding t))) ts)
    TSNullable ts     -> fromMaybe AE.null_
                       . getOp (interpretILan (\t -> Op (fmap (typeToEncoding t))) ts)
    TSTuple ts        -> AE.list id
                       . getOp (preDivisibleT (\t -> Op $ \x -> [withTSType_ typeToEncoding t x]) ts)
    TSObject    ts    -> A.pairs . getOp (objTypeToEncoding (TSObject ts))
    TSSingle ts       -> typeToEncoding ts
    TSUnion ts        -> iapply (withTSType_ typeToEncoding) ts
    TSNamedType (TSNamed _ nt) xs -> case nt of
      TSNFunc f -> typeToEncoding (tsApply f xs)
      TSNPrimType PS{..} -> namedPrimToEncoding psItem . psSerializer
    TSIntersection ts -> A.pairs . getOp (objTypeToEncoding (TSIntersection ts))
    TSPrimType PS{..} -> primToEncoding psItem . psSerializer

enumLitToValue :: EnumLit -> A.Value
enumLitToValue = \case
    ELString t -> A.String t
    ELNumber n -> A.Number n

primToValue :: TSPrim a -> a -> A.Value
primToValue = \case
    TSBoolean -> A.Bool
    TSNumber  -> A.Number
    -- hm...
    TSBigInt  -> A.Number . fromIntegral
    TSString  -> A.String
    -- TSEnum _ e -> \i -> enumLitToValue (snd (e Vec.! i))
    TSStringLit t -> \_ -> A.String t
    TSNumericLit n -> \_ -> A.Number n
    -- hm...
    TSBigIntLit n -> \_ -> A.Number (fromIntegral n)
    TSUnknown -> id
    TSAny -> id
    -- hm...
    TSVoid -> \_ -> A.Null
    TSUndefined -> \_ -> A.Null
    TSNull -> \_ -> A.Null
    TSNever -> absurd

namedPrimToValue :: TSNamedPrim a -> a -> A.Value
namedPrimToValue = \case
    TSEnum e -> \i -> enumLitToValue (snd (e Vec.! i))

objTypeToValue :: TSType 'Nat.Z 'IsObj Void a -> Op [A.Pair] a
objTypeToValue = \case
    TSObject       ts -> keyValToValue ts
    TSIntersection ts -> preDivisibleT objTypeToValue ts
    TSNamedType (TSNamed _ nt) xs -> case nt of
      TSNFunc f -> objTypeToValue (tsApply f xs)
  where
    keyValToValue :: TSKeyVal 'Nat.Z Void ~> Op [A.Pair]
    keyValToValue = preDivisibleT
        ( interpretObjMember
            (\k t -> Op           $ \x -> [k A..= withTSType_ typeToValue t x])
            (\k t -> Op . foldMap $ \x -> [k A..= withTSType_ typeToValue t x])
        )

typeToValue
    :: TSType 'Nat.Z k Void a -> a -> A.Value
typeToValue = \case
    TSArray ts        -> A.Array
                       . V.fromList
                       . getOp (interpretILan (\t -> Op ( map (typeToValue t))) ts)
    TSNullable ts     -> fromMaybe A.Null
                       . getOp (interpretILan (\t -> Op (fmap (typeToValue t))) ts)
    TSTuple ts        -> A.Array
                       . V.fromList
                       . getOp (preDivisibleT (\t -> Op $ \x -> [withTSType_ typeToValue t x]) ts)
    TSObject    ts    -> A.object . getOp (objTypeToValue (TSObject ts))
    TSSingle ts       -> typeToValue ts
    TSUnion ts        -> iapply (withTSType_ typeToValue) ts
    TSNamedType (TSNamed _ nt) xs -> case nt of
      TSNFunc f -> typeToValue (tsApply f xs)
      TSNPrimType PS{..} -> namedPrimToValue psItem . psSerializer
    TSIntersection ts -> A.object . getOp (objTypeToValue (TSIntersection ts))
    TSPrimType PS{..} -> primToValue psItem . psSerializer

data ParseErr = PEInvalidEnum   [(Text, EnumLit)]
              | PEInvalidString Text       Text
              | PEInvalidNumber Scientific Scientific
              | PEInvalidBigInt Integer    Integer
              | PEPrimitive     (Some TSPrim) Text
              | PENamedPrimitive (Some TSNamedPrim) Text
              | PEExtraTuple    Int        Int
              | PENotInUnion    [PP.Doc ()]
              | PENever
  deriving (Show)

parseEnumLit :: EnumLit -> ABE.Parse () ()
parseEnumLit = \case
    ELString t -> ABE.withText $ eqOrFail (const ()) t
    ELNumber t -> ABE.withScientific $ eqOrFail (const ()) t

eqOrFail :: Eq a => (a -> e) -> a -> a -> Either e ()
eqOrFail e x y
  | x == y    = Right ()
  | otherwise = Left (e y)

parsePrim :: TSPrim a -> ABE.Parse ParseErr a
parsePrim = \case
    TSBoolean   -> ABE.asBool
    TSNumber    -> ABE.asScientific
    TSBigInt    -> ABE.asIntegral
    TSString    -> ABE.asText
    TSStringLit t -> ABE.withText $ eqOrFail (PEInvalidString t) t
    TSNumericLit t -> ABE.withScientific $ eqOrFail (PEInvalidNumber t) t
    TSBigIntLit t -> ABE.withIntegral $ eqOrFail (PEInvalidBigInt t) t
    TSUnknown -> ABE.asValue
    TSAny -> ABE.asValue
    TSVoid -> ABE.asNull
    TSUndefined -> ABE.asNull
    TSNull -> ABE.asNull
    TSNever -> ABE.throwCustomError PENever

parseNamedPrim :: TSNamedPrim a -> ABE.Parse ParseErr a
parseNamedPrim = \case
    TSEnum es -> ABE.mapError (\_ -> PEInvalidEnum (toList es)) $ Vec.ifoldr
      (\i (_, e) ps -> (i <$ parseEnumLit e) ABE.<|> ps)
      (ABE.throwCustomError ())
      es

type Parse = ABE.ParseT ParseErr Identity

parseType
    :: forall k a. ()
    => TSType 'Nat.Z k Void a
    -> Parse a
parseType = \case
    TSArray ts -> unwrapFunctor $ interpretILan (WrapFunctor . ABE.eachInArray . parseType) ts
    TSNullable ts -> unwrapFunctor $ interpretILan (WrapFunctor . ABE.perhaps . parseType) ts
    TSTuple ts -> do
      (res, n) <- flip runStateT 0 $ (`interpret` ts) $ \t -> StateT $ \i ->
        (,i+1) <$> ABE.nth i (withTSType_ parseType t)
      ABE.withArray $ \xs ->
        if V.length xs > n
          then Left $ PEExtraTuple n (V.length xs)
          else pure res
    TSObject ts -> parseKeyVal ts
    TSSingle ts -> parseType ts
    TSUnion ts ->
      let us = []
      -- let us = icollect (withTSType_ (ppType Vec.VNil)) ts
      in  foldr @[] (ABE.<|>) (ABE.throwCustomError (PENotInUnion us)) $
            icollect (interpretPost (withTSType_ parseType)) (unPostT ts)
    TSNamedType (TSNamed _ nt) xs -> case nt of
      TSNFunc t -> parseType (tsApply t xs)
      TSNPrimType PS{..}
            -> either (ABE.throwCustomError . PENamedPrimitive (Some psItem)) pure . psParser
           =<< parseNamedPrim psItem
    -- TSApplied t f -> parseType (tsApply t f)
    TSIntersection ts -> interpret parseType ts
    TSPrimType PS{..} -> either (ABE.throwCustomError . PEPrimitive (Some psItem)) pure . psParser
                     =<< parsePrim psItem
  where
    parseKeyVal :: TSKeyVal 'Nat.Z Void ~> Parse
    parseKeyVal = interpret
        ( unwrapFunctor . interpretObjMember
            (\k -> WrapFunctor . ABE.key    k . withTSType_ parseType)
            (\k -> WrapFunctor . ABE.keyMay k . withTSType_ parseType)
        )

