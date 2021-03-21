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
  , ppTypeF'
  , ppTypeF
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

-- traverseTSType_
--     :: Functor f
--     => (forall k. TSType p k a -> f (TSType p k m b))
--     -> TSType_ p a
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

type TSKeyVal p = PreT Ap (ObjMember (TSType_ p))

data TSType :: Nat -> IsObjType -> Type -> Type where
    TSArray        :: ILan [] (TSType p k) a -> TSType p 'NotObj a
    TSNullable     :: ILan Maybe (TSType p k) a -> TSType p 'NotObj a
    TSTuple        :: PreT Ap (TSType_ p) a -> TSType p 'NotObj a
    TSObject       :: TSKeyVal p a -> TSType p 'IsObj a
    TSSingle       :: TSType p 'IsObj a -> TSType p 'NotObj a
    TSUnion        :: PostT Dec (TSType_ p) a -> TSType p 'NotObj a
    TSNamedType    :: TSNamed p k as a -> NP (TSType_ p) as -> TSType p k a
    TSVar          :: !(Fin p) -> TSType p 'NotObj a   -- is NotObj right?
    TSIntersection :: PreT Ap (TSType p 'IsObj) a -> TSType p 'IsObj a
    TSPrimType     :: PS TSPrim a -> TSType p 'NotObj a

data TSNameable :: Nat -> IsObjType -> [Type] -> Type -> Type where
    TSNFunc     :: TSTypeF p k as a -> TSNameable p k as a
    TSNPrimType :: PS TSNamedPrim a -> TSNameable p 'NotObj '[] a
    TSNExternal :: PS ((:~:) A.Value) a -> TSNameable p 'NotObj '[] a

instance Invariant (TSNameable p k as) where
    invmap f g = \case
      TSNFunc x     -> TSNFunc (invmap f g x)
      TSNPrimType x -> TSNPrimType (invmap f g x)
      TSNExternal x -> TSNExternal (invmap f g x)

data TSNamed_ p as a = forall k. TSNamed_ (TSNamed p k as a)

withTSNamed_
    :: (forall k. TSNamed p k as a -> r)
    -> TSNamed_ p as a
    -> r
withTSNamed_ f (TSNamed_ t) = f t

data TSNamed p k as a = TSNamed
    { tsnName :: Text
    , tsnType :: TSNameable p k as a
    }

instance Invariant (TSNamed p k as) where
    invmap f g (TSNamed n t) = TSNamed n (invmap f g t)

instance Invariant (TSNamed_ p as) where
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

data TSTypeF :: Nat -> IsObjType -> [Type] -> Type -> Type where
    TSGeneric
        :: NP (K Text) as
        -> (forall r. SNat_ r -> NP (TSType_ (Plus r p)) as -> TSType (Plus r p) k b)
        -> TSTypeF p k as b
    TSGenericInterface
        :: NP (K Text) as
        -> (forall r. SNat_ r -> NP (TSType_ (Plus r p)) as -> TSKeyVal (Plus r p) b)
        -> TSTypeF p 'IsObj as b

instance Invariant (TSTypeF p k as) where
    invmap f g (TSGeneric xs h) =
        TSGeneric xs (\q -> invmap f g . h q)
    invmap f g (TSGenericInterface xs h) =
        TSGenericInterface xs (\q -> invmap f g . h q)

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
      TSNamedType (TSNamed nm nt) xs -> case nt of
        TSNFunc tf     -> TSNamedType (TSNamed nm (TSNFunc     (invmap f g tf))) xs
        TSNPrimType ps -> TSNamedType (TSNamed nm (TSNPrimType (invmap f g ps))) xs
        TSNExternal ps -> TSNamedType (TSNamed nm (TSNExternal (invmap f g ps))) xs
      TSVar i -> TSVar i
      TSIntersection ts -> TSIntersection (invmap f g ts)
      TSPrimType p -> TSPrimType (invmap f g p)

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

tsApply
    :: TSTypeF p k as b      -- ^ type function
    -> NP (TSType_ p) as     -- ^ thing to apply
    -> TSType p k b
tsApply (TSGeneric _ f) t = f SZ_ t
tsApply (TSGenericInterface _ f) t = TSObject (f SZ_ t)
-- tsApply p@(TSPrimTypeF _ _) _ = TSApplied pil

tsApply1
    :: TSTypeF p k '[a] b      -- ^ type function
    -> TSType_ p a         -- ^ thing to apply
    -> TSType p k b
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
    :: forall p k a b r. ()
    => TSTypeF p k '[a] b
    -> (TSType ('Nat.S p) k b -> r)
    -> r
tsApplyVar1 (TSGeneric _ g) f =
    f (g (SS_ SZ_) (TSType_ (TSVar FZ) :* Nil))
tsApplyVar1 (TSGenericInterface _ g) f =
    f (TSObject (g (SS_ SZ_) (TSType_ (TSVar FZ) :* Nil)))

tsApplyVar
    :: forall p k as b r. ()
    => TSTypeF p k as b
    -> (forall s. Vec s Text -> TSType (Plus s p) k b -> r)
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
        TSNExternal ps -> TSNamedType (TSNamed nm (TSNExternal ps)) Nil
      TSIntersection t -> TSIntersection (hmap go t)
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
    :: TSType p k a
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
      TSNExternal _                  -> SNotObj
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
    :: TSType 'Nat.Z k a
    -> PP.Doc x
ppType = ppType' Vec.VNil

ppType'
    :: forall p k a x. ()
    => Vec p Text
    -> TSType p k a
    -> PP.Doc x
ppType' = go
  where
    go :: Vec q Text -> TSType q j b -> PP.Doc x
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
      TSPrimType PS{..} -> ppPrim psItem

-- TODO: these typeF should probably be TSName instead of TSTypeF
ppTypeF
    :: Text
    -> TSTypeF 'Nat.Z k a b
    -> PP.Doc x
ppTypeF nm = ppTypeF' nm Vec.VNil

-- TODO: figure out shadowing
ppTypeF'
    :: Text
    -> Vec p Text
    -> TSTypeF p k a b
    -> PP.Doc x
ppTypeF' n ps tf@(TSGeneric vs _) = PP.hsep [
      "type"
        PP.<+> PP.pretty n
        PP.<> (if null args then ""
                            else PP.encloseSep "<" ">" "," args
              )
    , "="
    , tsApplyVar tf $ \rs -> ppType' (rs Vec.++ ps)
    ]
  where
    args = htoList (PP.pretty . SOP.unK) vs
ppTypeF' n ps tf@(TSGenericInterface vs _) = PP.hsep [
      "interface"
        PP.<> PP.pretty n
        PP.<> (if null args then ""
                            else PP.encloseSep "<" ">" "," args
              )
    , "="
    , tsApplyVar tf $ \rs -> ppType' (rs Vec.++ ps)
    ]
  where
    args = htoList (PP.pretty . SOP.unK) vs

typeExports_
    :: TSType_ 'Nat.Z a
    -> PP.Doc x
typeExports_ = withTSType_ typeExports

typeExports
    :: TSType 'Nat.Z k a
    -> PP.Doc x
typeExports = typeExports' Vec.VNil

typeExports'
    :: Vec p Text
    -> TSType p k a
    -> PP.Doc x
typeExports' ps = ppMap . flattenType ps

namedTypeExports
    :: TSNamed 'Nat.Z k as a
    -> PP.Doc x
namedTypeExports = namedTypeExports' Vec.VNil

namedTypeExports'
    :: Vec p Text
    -> TSNamed p k as a
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
    -> TSNamed p k as a
    -> Map Text (Set Text, PP.Doc x)
flattenNamedType ps t = execState (flattenNamedType_ ps t) M.empty

-- | Ignores the top level type, so why even bother?
flattenType
    :: Vec p Text
    -> TSType p k a
    -> Map Text (Set Text, PP.Doc x)
flattenType ps t = execState (flattenType_ ps t) M.empty

flattenNamedType_
    :: forall p k a as x. ()
    => Vec p Text
    -> TSNamed p k as a
    -> State (Map Text (Set Text, PP.Doc x)) (Set Text)
flattenNamedType_ ps TSNamed{..} = case tsnType of
    TSNFunc tsf -> do
      deps <- tsApplyVar tsf $ \rs t -> flattenType_ (rs Vec.++ ps) t
      modify $ M.insert tsnName $
        (deps, ppTypeF' tsnName ps tsf)
      pure deps
    TSNPrimType PS{..} -> do
      modify $ M.insert tsnName (S.empty, ppNamedPrim tsnName psItem)
      pure S.empty
    TSNExternal _ -> pure S.empty

flattenType_
    :: forall p k a x. ()
    => Vec p Text
    -> TSType p k a
    -> State (Map Text (Set Text, PP.Doc x)) (Set Text)
flattenType_ ps = go
  where
    go  :: forall j b. ()
        => TSType p j b
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

objTypeToEncoding :: TSType 'Nat.Z 'IsObj a -> Op A.Series a
objTypeToEncoding = \case
    TSObject       ts -> keyValToValue ts
    TSIntersection ts -> preDivisibleT objTypeToEncoding ts
    TSNamedType (TSNamed _ nt) xs -> case nt of
      TSNFunc f -> objTypeToEncoding (tsApply f xs)
  where
    keyValToValue :: TSKeyVal 'Nat.Z ~> Op A.Series
    keyValToValue = preDivisibleT
        ( interpretObjMember
            (\k t -> Op           $ \x -> k A..= withTSType_ typeToValue t x)
            (\k t -> Op . foldMap $ \x -> k A..= withTSType_ typeToValue t x)
        )

typeToEncoding :: TSType 'Nat.Z k a -> a -> A.Encoding
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
      TSNExternal PS{..} -> AE.value . castWith (sym psItem) . psSerializer
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

objTypeToValue :: TSType 'Nat.Z 'IsObj a -> Op [A.Pair] a
objTypeToValue = \case
    TSObject       ts -> keyValToValue ts
    TSIntersection ts -> preDivisibleT objTypeToValue ts
    TSNamedType (TSNamed _ nt) xs -> case nt of
      TSNFunc f -> objTypeToValue (tsApply f xs)
  where
    keyValToValue :: TSKeyVal 'Nat.Z ~> Op [A.Pair]
    keyValToValue = preDivisibleT
        ( interpretObjMember
            (\k t -> Op           $ \x -> [k A..= withTSType_ typeToValue t x])
            (\k t -> Op . foldMap $ \x -> [k A..= withTSType_ typeToValue t x])
        )

typeToValue
    :: TSType 'Nat.Z k a -> a -> A.Value
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
      TSNExternal PS{..} -> castWith (sym psItem) <$> psSerializer
    TSIntersection ts -> A.object . getOp (objTypeToValue (TSIntersection ts))
    TSPrimType PS{..} -> primToValue psItem . psSerializer

data ParseErr = PEInvalidEnum   [(Text, EnumLit)]
              | PEInvalidString Text       Text
              | PEInvalidNumber Scientific Scientific
              | PEInvalidBigInt Integer    Integer
              | PEPrimitive     (Some TSPrim) Text
              | PENamedPrimitive (Some TSNamedPrim) Text
              | PEExternal      Text       Text
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
    => TSType 'Nat.Z k a
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
    TSNamedType (TSNamed nm nt) xs -> case nt of
      TSNFunc t -> parseType (tsApply t xs)
      TSNPrimType PS{..}
            -> either (ABE.throwCustomError . PENamedPrimitive (Some psItem)) pure . psParser
           =<< parseNamedPrim psItem
      TSNExternal PS{..}
            -> either (ABE.throwCustomError . PEExternal nm) pure . psParser . castWith psItem
           =<< ABE.asValue
    TSIntersection ts -> interpret parseType ts
    TSPrimType PS{..} -> either (ABE.throwCustomError . PEPrimitive (Some psItem)) pure . psParser
                     =<< parsePrim psItem
  where
    parseKeyVal :: TSKeyVal 'Nat.Z ~> Parse
    parseKeyVal = interpret
        ( unwrapFunctor . interpretObjMember
            (\k -> WrapFunctor . ABE.key    k . withTSType_ parseType)
            (\k -> WrapFunctor . ABE.keyMay k . withTSType_ parseType)
        )

