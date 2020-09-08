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
  , EnumLit(..)
  , TSType(..)
  , TSType_(..)
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
  , compGeneric
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
  , typeFExports'
  , typeFExports
  , typeFExports_
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
    TSEnum       :: Text -> Vec n (Text, EnumLit) -> TSPrim (Fin n)
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

traverseTSType_
    :: Functor f
    => (forall k. TSType p k n a -> f (TSType p k m b))
    -> TSType_ p n a
    -> f (TSType_ p m b)
traverseTSType_ f (TSType_ t) = TSType_ <$> f t

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
    TSNamed        :: Text -> TSType p k n a -> TSType p k n a
    TSInterface    :: Text -> TSKeyVal p n a  -> TSType p 'IsObj n a
    TSApplied      :: TSTypeF p k n as b -> NP (TSType_ p n) as -> TSType p k n b
    TSVar          :: !(Fin p) -> TSType p 'NotObj n a   -- is NotObj right?
    TSIntersection :: PreT Ap (TSType p 'IsObj n) a -> TSType p 'IsObj n a
    TSExternal     :: SIsObjType k -> !n -> [Text] -> TSType p k n a
    TSPrimType     :: PS TSPrim a -> TSType p 'NotObj n a

-- TODO: this could be an interface, but only if it is an object literal
data TSTypeF :: Nat -> IsObjType -> Type -> [Type] -> Type -> Type where
    TSGeneric
        :: { tsgName    :: Text
           , tsgObjType :: SIsObjType k
           , tsgParams  :: NP (K Text) as
           , tsgFunc    :: forall r. SNat_ r -> NP (TSType_ (Plus r p) n) as -> TSType (Plus r p) k n b
           } -> TSTypeF p k n as b

compGeneric
    :: (forall r. SNat_ r -> TSType (Plus r p) k n b -> TSType (Plus r p) k n c)
    -> TSTypeF p k n as b
    -> TSTypeF p k n as c
compGeneric f (TSGeneric t o p g) =
    TSGeneric t o p (\q -> f q . g q)

instance Invariant (TSTypeF p k n as) where
    invmap f g (TSGeneric n o xs h) =
        TSGeneric n o xs (\q -> invmap f g . h q)

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
      TSNamed n t -> TSNamed n (invmap f g t)
      TSInterface n t -> TSInterface n (invmap f g t)
      TSApplied tf tx -> TSApplied (invmap f g tf) tx
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
    -> NP (TSType_ p n) as         -- ^ thing to apply
    -> TSType p k n b
tsApply (TSGeneric _ _ _ f) t = f SZ_ t

tsApply1
    :: TSTypeF p k n '[a] b      -- ^ type function
    -> TSType_ p n a         -- ^ thing to apply
    -> TSType p k n b
tsApply1 (TSGeneric _ _ _ f) t = f SZ_ (t :* Nil)

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
tsApplyVar1 (TSGeneric _ _ _ g) f =
    f (g (SS_ SZ_) (TSType_ (TSVar FZ) :* Nil))

tsApplyVar
    :: forall p k n as b r. ()
    => TSTypeF p k n as b
    -> (forall s. Vec s Text -> TSType (Plus s p) k n b -> r)
    -> r
tsApplyVar (TSGeneric _ _ ps g) f = withParams ps $ \rs es ->
     f (fmap (shadow oldVars) rs)
       (g (vecToSNat_ rs) (hmap (TSType_ . TSVar . weakenFin @_ @p . SOP.unK) es))
  where
    oldVars :: S.Set Text
    oldVars = S.fromList (htoList SOP.unK ps)

shadow :: S.Set Text -> Text -> Text
shadow ps t0 = go Nothing
  where
    go i
        | t `S.member` ps = go (Just (maybe 0 (+1) i))
        | otherwise       = t
      where
        t = appendNum i t0
    appendNum Nothing  = id
    appendNum (Just i) = (<> T.pack (show @Int i))


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
      TSNamed m t -> TSNamed m (go t)
      TSInterface m t -> TSInterface m (hmap (hmap (mapTSType_ go)) t)
      TSApplied (TSGeneric m o ps tf) txs ->
            TSApplied
              (TSGeneric m o ps $ \q ->
                case assocPlus @_ @r @q q of
                  Refl -> tf (plusNat q n)
              )
              (hmap (mapTSType_ go) txs)
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
    TSNamed _ t                   -> tsObjType t
    TSInterface _ _               -> SIsObj
    TSApplied (TSGeneric _ o _ _) _ -> o
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
      TSNamed n t       -> TSNamed n (go t)
      TSInterface n t   -> TSInterface n (hmap (hmap (mapTSType_ go)) t)
      TSApplied (TSGeneric n o p h) t -> TSApplied
        (TSGeneric n o p (\q -> go . h q . hmap (mapTSType_ (mapName g f))))
        (hmap (mapTSType_ go) t)
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
    TSEnum n es    -> PP.fillSep
      [ "enum"
      , PP.pretty n
      , PP.encloseSep "{" "}" ","
          [ PP.pretty e PP.<+> "=" PP.<+> ppEnumLit x
          | (e, x) <- toList es
          ]
      ]
    TSStringLit t  -> PP.pretty (show t)
    TSNumericLit n -> ppScientific n
    TSBigIntLit n  -> PP.pretty n
    TSUnknown      -> "unknown"
    TSAny          -> "any"
    TSVoid         -> "void"
    TSUndefined    -> "undefined"
    TSNull         -> "null"
    TSNever        -> "never"

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
      TSNamed n _ -> PP.pretty n
      TSInterface n _ -> PP.pretty n
      -- this is the benefit of delaying application
      TSApplied (TSGeneric n _ _ _) xs -> PP.pretty n <> PP.encloseSep "<" ">" ","
        (htoList (withTSType_ (go ps)) xs)
      TSVar i -> PP.pretty (ps Vec.! i)
      TSIntersection ts  -> PP.encloseSep "" "" " & " (htoList (go ps) ts)
      TSExternal _ n qs -> f n <>
        if null qs
          then mempty
          else PP.encloseSep "<" ">" "," (PP.pretty <$> qs)
      TSPrimType PS{..} -> ppPrim psItem

ppTypeF
    :: PP.Pretty n
    => TSTypeF_ 'Nat.Z n a b
    -> PP.Doc x
ppTypeF = ppTypeF' Vec.VNil

ppTypeF'
    :: PP.Pretty n
    => Vec p Text
    -> TSTypeF_ p n a b
    -> PP.Doc x
ppTypeF' ps = withTSTypeF_ (ppTypeFWith PP.pretty ps)

-- TODO: figure out shadowing
ppTypeFWith
    :: (n -> PP.Doc x)
    -> Vec p Text
    -> TSTypeF p k n a b
    -> PP.Doc x
ppTypeFWith f ps tf@(TSGeneric n _ vs _) = PP.hsep [
      PP.pretty n PP.<> PP.encloseSep "<" ">" "," (htoList (PP.pretty . SOP.unK) vs)
    , "="
    , tsApplyVar tf $ \rs -> ppTypeWith f (rs Vec.++ ps)
    ]

typeExports_
    :: Maybe Text    -- ^ top-level name and interface, if meant to be included
    -> TSType_ 'Nat.Z Void a
    -> PP.Doc x
typeExports_ iin0 = withTSType_ (typeExports (fmap (NotInterface,) iin0))

typeExports
    :: Maybe (IsInterface (k :~: 'IsObj), Text)    -- ^ top-level name and interface, if meant to be included
    -> TSType 'Nat.Z k Void a
    -> PP.Doc x
typeExports = typeExports' Vec.VNil

typeExports'
    :: Vec p Text
    -> Maybe (IsInterface (k :~: 'IsObj), Text)    -- ^ top-level name and interface, if meant to be included
    -> TSType p k Void a
    -> PP.Doc x
typeExports' ps iin0 ts =
      ppMap
    . maybe id (`M.insert` (params0, ppTypeWith PP.pretty ps t0)) (first void <$> iin0)
    $ tmap0
  where
    ((params0, t0), tmap0) = flattenType ps (\qs -> ppTypeWith PP.pretty (qs Vec.++ ps)) ts

typeFExports_
    :: Maybe Text    -- ^ top-level name, if meant to be included
    -> TSTypeF_ 'Nat.Z Void a b
    -> PP.Doc x
typeFExports_ iin0 = withTSTypeF_ (typeFExports (fmap (NotInterface,) iin0))

typeFExports
    :: Maybe (IsInterface (k :~: 'IsObj), Text)    -- ^ top-level name and interface, if meant to be included
    -> TSTypeF 'Nat.Z k Void a b
    -> PP.Doc x
typeFExports = typeFExports' Vec.VNil

typeFExports'
    :: Vec p Text
    -> Maybe (IsInterface (k :~: 'IsObj), Text)    -- ^ top-level name and interface, if meant to be included
    -> TSTypeF p k Void a b
    -> PP.Doc x
typeFExports' ps iin0 tf = tsApplyVar tf $ \rs ts ->
  let ((params0, t0), tmap0) = flattenType (rs Vec.++ ps) (\qs -> ppTypeWith PP.pretty (qs Vec.++ (rs Vec.++ ps))) ts
  in    ppMap
      . maybe id (`M.insert` (toList rs ++ params0, ppTypeWith PP.pretty (rs Vec.++ ps) t0)) (first void <$> iin0)
      $ tmap0

ppMap
    :: PP.Pretty n
    => Map (IsInterface (), n) ([Text], PP.Doc x)
    -> PP.Doc x
ppMap mp = PP.vcat
    [ PP.hsep [
        "export"
      , iiString ii
      , PP.pretty n <>
          (if null params
              then mempty
              else PP.encloseSep "<" ">" "," (PP.pretty <$> params)
          )
      , "="
      , tDoc
      ]
    | ((ii, n), (params, tDoc)) <- M.toList mp
    ]
  where
    iiString = \case
      NotInterface  -> "type"
      IsInterface _ -> "interface"

-- | Pull out all of the named types to be top-level type declarations, and
-- have create a map of all of those declarations.
flattenType
    :: Vec p Text
    -> (forall q j b. Vec q Text -> TSType (Plus q p) j Text b -> r)
    -> TSType p k Void a
    -> (([Text], TSType p k Text a), Map (IsInterface (), Text) ([Text], r))
flattenType ps f t = runState (flattenType_ ps f t) M.empty

flattenType_
    :: forall p k a r. ()
    => Vec p Text
    -> (forall q j b. Vec q Text -> TSType (Plus q p) j Text b -> r)
    -> TSType p k Void a
    -> State (Map (IsInterface (), Text) ([Text], r)) ([Text], TSType p k Text a)
flattenType_ ps f = go Vec.VNil
  where
    go  :: forall q j b. ()
        => Vec q Text
        -> TSType (Plus q p) j Void b
        -> State (Map (IsInterface (), Text) ([Text], r)) ([Text], TSType (Plus q p) j Text b)
    go qs = \case
      TSArray t  -> ([],) . TSArray <$> htraverse (fmap snd . go qs) t
      TSNullable t  -> ([],) . TSNullable <$> htraverse (fmap snd . go qs) t
      TSTuple ts -> ([],) . TSTuple <$> htraverse (traverseTSType_ (fmap snd . go qs)) ts
      TSObject ts -> do
        ([],) . TSObject <$> htraverse (htraverse (traverseTSType_ (fmap snd . go qs))) ts
      TSSingle ts -> second TSSingle <$> go qs ts
      TSUnion ts -> ([],) . TSUnion <$> htraverse (traverseTSType_ (fmap snd . go qs)) ts
      TSApplied tf@(TSGeneric n o ms _) t -> do
        t' <- htraverse (traverseTSType_ (fmap snd . go qs)) t
        tsApplyVar tf $ \(rs :: Vec rs Text) tv ->
          (case assocPlus @rs @q @p (vecToSNat_ rs) of
            Refl -> do
              (_, res) <- go (rs Vec.++ qs) tv
              modify $ M.insert (NotInterface, n)
                (htoList SOP.unK ms, f (rs Vec.++ qs) res)
          ) :: State (Map (IsInterface (), Text) ([Text], r)) ()
        pure ([], TSExternal o n (htoList (withTSType_ (T.pack . show . ppTypeWith PP.pretty (qs Vec.++ ps))) t'))
      TSNamed n t -> do
        (_, res) <- go qs t
        modify $ M.insert (NotInterface, n) ([], f qs res)
        pure ([], TSExternal (tsObjType t) n [])
      TSInterface n ts -> do
        res <- TSObject <$> htraverse (htraverse (traverseTSType_ (fmap snd . go qs))) ts
        modify $ M.insert (IsInterface(), n) ([], f qs res)
        pure ([], TSExternal SIsObj n [])
      TSVar i -> pure ([], TSVar i)
      TSIntersection ts -> ([],) . TSIntersection <$> htraverse (fmap snd . go qs) ts
      TSPrimType p -> pure ([], TSPrimType p)

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
    TSEnum _ e -> \i -> encodeEnumLit (snd (e Vec.! i))
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

objTypeToEncoding :: TSType 'Nat.Z 'IsObj Void a -> Op A.Series a
objTypeToEncoding = \case
    TSObject       ts -> keyValToValue ts
    TSIntersection ts -> preDivisibleT objTypeToEncoding ts
    TSInterface _ ts  -> keyValToValue ts
    TSNamed     _   t -> objTypeToEncoding t
    TSApplied   f   t -> objTypeToEncoding (tsApply f t)
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
    TSNamed _ t       -> typeToEncoding t
    TSInterface n ts  -> A.pairs . getOp (objTypeToEncoding (TSInterface n ts))
    TSApplied f t     -> typeToEncoding (tsApply f t)
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
    TSEnum _ e -> \i -> enumLitToValue (snd (e Vec.! i))
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

objTypeToValue :: TSType 'Nat.Z 'IsObj Void a -> Op [A.Pair] a
objTypeToValue = \case
    TSObject       ts -> keyValToValue ts
    TSIntersection ts -> preDivisibleT objTypeToValue ts
    TSInterface _ ts  -> keyValToValue ts
    TSNamed     _   t -> objTypeToValue t
    TSApplied     f   t -> objTypeToValue (tsApply f t)
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
    TSNamed _ t       -> typeToValue t
    TSInterface n ts  -> A.object . getOp (objTypeToValue (TSInterface n ts))
    TSApplied f t       -> typeToValue (tsApply f t)
    TSIntersection ts -> A.object . getOp (objTypeToValue (TSIntersection ts))
    TSPrimType PS{..} -> primToValue psItem . psSerializer

data ParseErr = PEInvalidEnum   [(Text, EnumLit)]
              | PEInvalidString Text       Text
              | PEInvalidNumber Scientific Scientific
              | PEInvalidBigInt Integer    Integer
              | PEPrimitive     (Some TSPrim) Text
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
    TSEnum _ es -> ABE.mapError (\_ -> PEInvalidEnum (toList es)) $ Vec.ifoldr
      (\i (_, e) ps -> (i <$ parseEnumLit e) ABE.<|> ps)
      (ABE.throwCustomError ())
      es
    TSStringLit t -> ABE.withText $ eqOrFail (PEInvalidString t) t
    TSNumericLit t -> ABE.withScientific $ eqOrFail (PEInvalidNumber t) t
    TSBigIntLit t -> ABE.withIntegral $ eqOrFail (PEInvalidBigInt t) t
    TSUnknown -> ABE.asValue
    TSAny -> ABE.asValue
    TSVoid -> ABE.asNull
    TSUndefined -> ABE.asNull
    TSNull -> ABE.asNull
    TSNever -> ABE.throwCustomError PENever

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
    TSNamed _ t -> parseType t
    TSInterface _ ts -> parseKeyVal ts
    TSApplied t f -> parseType (tsApply t f)
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

