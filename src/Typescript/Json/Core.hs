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
  -- * prettyprint
  , ppEnumLit
  , ppPrim
  , ppType'
  , ppType
  , ppNamed'
  , ppNamed
  , typeExports'
  , typeExports
  , typeExports_
  , namedTypeExports'
  , namedTypeExports
  , namedTypeExports_
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
  , reAssign
  , isAssignable
  , eqTSPrim
  ) where

import           Control.Applicative
import           Control.Applicative.Free
import           Control.Monad
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Fin                                  (Fin(..))
import           Data.Foldable
import           Data.Functor
import           Data.Functor.Combinator hiding            (Comp(..))
import           Data.Functor.Compose
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divisible.Free (Dec1(..))
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.GADT.Show
import           Data.HFunctor.Route
import           Data.Kind
import           Data.Map                                  (Map)
import           Data.Maybe
import           Data.Ord
import           Data.Profunctor
import           Data.Proxy
import           Data.SOP                                  (NP(..), K(..))
import           Data.Scientific                           (Scientific, toBoundedInteger)
import           Data.Semigroup                            (First(..))
import           Data.Set                                  (Set)
import           Data.Some                                 (Some(..))
import           Data.Text                                 (Text)
import           Data.Type.Equality
import           Data.Type.Nat
import           Data.Vec.Lazy                             (Vec(..))
import           Data.Void
import           Typescript.Json.Core.Combinators
import qualified Data.Aeson                                as A
import qualified Data.Aeson.BetterErrors                   as ABE
import qualified Data.Aeson.Encoding                       as AE
import qualified Data.Aeson.Types                          as A
import qualified Data.Fin                                  as Fin
import qualified Data.Functor.Combinator.Unsafe            as FCU
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
    TSNamedType    :: TSNamed p k as a -> NP (TSType_ p) as -> TSType p k a
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
    Nil -> \f -> f VNil Nil
    K p :* ps -> \f -> withParams ps $ \bs (es :: NP (K (Fin bs)) as) ->
      f (p ::: bs) (K FZ :* hmap (K . FS . SOP.unK) es)

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
       (g (vecToSNat_ rs) (hmap (TSType_ . TSVar . weakenFin @_ @p . SOP.unK) es))
tsApplyVar (TSGenericInterface ps g) f = withParams ps $ \rs es ->
     f rs
       (TSObject (g (vecToSNat_ rs) (hmap (TSType_ . TSVar . weakenFin @_ @p . SOP.unK) es)))

vecToSNat_ :: forall n b. Vec n b -> SNat_ n
vecToSNat_ = \case
    VNil     -> SZ_
    _ ::: xs -> SS_ (vecToSNat_ xs)

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
ppType = ppType' VNil

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
      -- TODO: hm, should this be not a primitive?
      -- i guess in a sense it does matter because of optional chaining?
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

ppNamed
    :: TSNamed 'Nat.Z k as a
    -> PP.Doc x
ppNamed = ppNamed' VNil

ppNamed'
    :: Vec p Text
    -> TSNamed p k as a
    -> PP.Doc x
ppNamed' ps TSNamed{..} = case tsnType of
    TSNFunc tsf -> case tsf of
      TSGeneric vs _ ->
        let args = htoList (PP.pretty . SOP.unK) vs
        in  PP.hsep [
              "type"
                PP.<+> PP.pretty tsnName
                PP.<> (if null args then ""
                                    else PP.encloseSep "<" ">" "," args
                      )
            , "="
            , tsApplyVar tsf $ \rs -> ppType' (rs Vec.++ ps)
            ]
      TSGenericInterface vs _ ->
        let args = htoList (PP.pretty . SOP.unK) vs
        in  PP.hsep [
              "interface"
                PP.<+> PP.pretty tsnName
                PP.<> (if null args then ""
                                    else PP.encloseSep "<" ">" "," args
                      )
            , "="
            , tsApplyVar tsf $ \rs -> ppType' (rs Vec.++ ps)
            ]
    TSNPrimType PS{..} -> ppNamedPrim tsnName psItem

typeExports_
    :: TSType_ 'Nat.Z a
    -> PP.Doc x
typeExports_ = withTSType_ typeExports

typeExports
    :: TSType 'Nat.Z k a
    -> PP.Doc x
typeExports = typeExports' VNil

typeExports'
    :: Vec p Text
    -> TSType p k a
    -> PP.Doc x
typeExports' ps = ppMap . flattenType ps

namedTypeExports_
    :: TSNamed_ 'Nat.Z as a
    -> PP.Doc x
namedTypeExports_ = withTSNamed_ namedTypeExports

namedTypeExports
    :: TSNamed 'Nat.Z k as a
    -> PP.Doc x
namedTypeExports = namedTypeExports' VNil

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
flattenNamedType_ ps tsn@TSNamed{..} = case tsnType of
    TSNFunc tsf -> do
      deps <- tsApplyVar tsf $ \rs t -> flattenType_ (rs Vec.++ ps) t
      modify $ M.insert tsnName (deps, pp)
      pure deps
    TSNPrimType PS{..} -> do
      modify $ M.insert tsnName (S.empty, pp)
      pure S.empty
  where
    pp = ppNamed' ps tsn

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
    TSIntersection ts -> A.object . getOp (objTypeToValue (TSIntersection ts))
    TSPrimType PS{..} -> primToValue psItem . psSerializer

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

showParseErr :: ParseErr -> String
showParseErr = show -- TODO

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
      let us = icollect (withTSType_ ppType) ts
      in  foldr @[] (ABE.<|>) (ABE.throwCustomError (PENotInUnion us)) $
            icollect (interpretPost (withTSType_ parseType)) (unPostT ts)
    TSNamedType (TSNamed nm nt) xs -> case nt of
      TSNFunc t -> parseType (tsApply t xs)
      TSNPrimType PS{..}
            -> either (ABE.throwCustomError . PENamedPrimitive nm (Some psItem)) pure . psParser
           =<< parseNamedPrim psItem
                        -- remove this unsafeApply if ParseT ever gets an Apply instance
    TSIntersection ts -> FCU.unsafeApply (Proxy @(ABE.ParseT ParseErr Identity)) $
        interpret parseType ts
    TSPrimType PS{..} -> either (ABE.throwCustomError . PEPrimitive (Some psItem)) pure . psParser
                     =<< parsePrim psItem
  where
    parseKeyVal :: TSKeyVal 'Nat.Z ~> Parse
    parseKeyVal = interpret
        ( unwrapFunctor . interpretObjMember
            (\k -> WrapFunctor . ABE.key    k . withTSType_ parseType)
            (\k -> WrapFunctor . ABE.keyMay k . withTSType_ parseType)
        )

-- | answers: is X assignable to Y?
--
-- actually maybe we should even have a "convert" functionality... so no
-- boolean blindness
--
-- https://basarat.gitbook.io/typescript/type-system/type-compatibility
isAssignable :: TSType 'Nat.Z k a -> TSType 'Nat.Z j b -> Bool
isAssignable t u = isJust $ reAssign t u

-- | a can be assigned as a b.  the function will "lose" information.
--
-- assumes --stictNullChecks
-- https://www.typescriptlang.org/docs/handbook/type-compatibility.html#advanced-topics
reAssignPrim :: (r -> a) -> TSPrim a -> TSType 'Nat.Z k b -> Maybe (r -> Either Text b)
reAssignPrim z = \case
    TSBoolean -> \case
      TSPrimType (PS TSBoolean f _) -> Just $ f . z
      _ -> Nothing
    TSNumber -> \case
      TSPrimType (PS TSNumber f _) -> Just $ f . z
      -- compatible with num as long as there is at least one number, or is
      -- empty.  this is different than the spec but w/e
      TSNamedType (TSNamed{..}) _ -> case tsnType of
        TSNPrimType (PS (TSEnum cs) f _)
          | null cs   -> Just $ \_ -> Left $ "Number out of range for empty Enum"
          | otherwise -> do
              let numberOpts =
                    [ (i, n)
                    | (i, (_, ELNumber n)) <- Vec.toList $ Vec.imap (,) cs
                    ]
              guard $ not (null numberOpts)
              pure $ \(z->m) ->
                case getFirst <$> foldMap (\(i, n) -> First i <$ guard (n == m)) numberOpts of
                  Nothing -> Left $ "Number " <> T.pack (show m) <> " out of range for Enum: " <> T.pack (show cs)
                  Just x  -> f x
        TSNFunc _ -> Nothing
      _ -> Nothing
    TSBigInt -> \case
      TSPrimType (PS TSBigInt f _) -> Just $ f . z
      _ -> Nothing
    TSString -> \case
      TSPrimType (PS TSString f _) -> Just $ f . z
      _ -> Nothing
    TSStringLit s -> \case
      TSPrimType (PS (TSStringLit t) f _) -> f . z <$ guard (s == t)
      _ -> Nothing
    TSNumericLit s -> \case
      TSPrimType (PS (TSNumericLit t) f _) -> f . z <$ guard (s == t)
      _ -> Nothing
    TSBigIntLit s -> \case
      TSPrimType (PS (TSBigIntLit t) f _) -> f . z <$ guard (s == t)
      _ -> Nothing
    TSUnknown -> \case
      TSPrimType (PS TSUnknown f _) -> Just $ f . z
      _ -> Nothing
    TSAny -> \case
      TSPrimType (PS TSNever _ _) -> Nothing
      t -> Just $ first (T.unlines . ABE.displayError (T.pack . showParseErr)) . ABE.parseValue (parseType t) . z
    TSVoid -> \case
      TSPrimType (PS TSAny f _) -> Just $ \_ -> f A.Null
      TSPrimType (PS TSUnknown f _) -> Just $ \_ -> f A.Null
      TSPrimType (PS TSVoid f _) -> Just $ f . z
      _ -> Nothing
    TSUndefined -> \case
      TSPrimType (PS TSAny f _) -> Just $ \_ -> f A.Null
      TSPrimType (PS TSUnknown f _) -> Just $ \_ -> f A.Null
      TSPrimType (PS TSVoid f _) -> Just $ f . z
      TSPrimType (PS TSUndefined f _) -> Just $ f . z
      _ -> Nothing
    TSNull -> \case
      TSPrimType (PS TSAny f _) -> Just $ \_ -> f A.Null
      TSPrimType (PS TSUnknown f _) -> Just $ \_ -> f A.Null
      TSPrimType (PS TSNull f _) -> Just $ f . z
      _ -> Nothing
    -- never can be anything
    TSNever -> \_ -> Just $ Right . absurd . z


-- | converts a Nullable x to x | null
unNullable :: ILan Maybe (TSType p k) a -> TSType p 'NotObj a
unNullable (ILan f g t) = TSUnion $ PostT $
    Dec1 (maybe (Right ()) Left . g) (f . Just :<$>: TSType_ t) $
      injectPost (\_ -> f Nothing) $ TSType_ (TSPrimType (inject TSNull))

-- | If X is assignable to Y, then convert x to the more general y,
-- potentially losing information.
reAssign :: TSType 'Nat.Z k a -> TSType 'Nat.Z j b -> Maybe (a -> Either Text b)
reAssign t0 = case t0 of
    TSArray (ILan _ g t) -> loopReAssign t0 $ \case
      TSArray (ILan f' _ u) ->
        dimap g (fmap f' . sequence) . map <$> reAssign t u
      _ -> Nothing
    -- this is going to be funky
    TSNullable t -> reAssign (unNullable t)
    TSTuple (PreT xs) -> loopReAssign t0 $ \case
      TSTuple (PreT ys) -> reAssignTuple xs ys
      _ -> Nothing
    TSObject xs -> reAssignIsObj (TSObject xs)
    TSSingle x -> loopReAssign t0 (reAssign x)
    TSUnion (PostT xs) -> \y -> fmap getOp . getCompose $
      interpret (withTSType_ (Compose . fmap Op . (`reAssign` y)) . getPost) xs
    TSIntersection xs -> reAssignIsObj (TSIntersection xs)
    TSNamedType TSNamed{..} ps -> case tsnType of
      TSNFunc tf -> reAssign (tsApply tf ps)
      TSNPrimType (PS{..}) -> case psItem of
        TSEnum cs -> loopReAssign t0 $ \case
          -- compatible with num as long as there is at least one number, or is
          -- empty.  this is different than the spec but w/e
          TSPrimType (PS TSNumber f _) -> case cs of
            VNil -> Just $ \i -> Right $ Fin.absurd (psSerializer i)
            _ ->
              let numberOpts =
                    [ (i, n)
                    | (i, (_, ELNumber n)) <- Vec.toList $ Vec.imap (,) cs
                    ]
              in  guard (not (null numberOpts)) $> \i ->
                     case snd $ cs Vec.! psSerializer i of
                       ELNumber n -> f n
                       ELString s -> Left $ "Enum mismatch: expected number, got " <> s
          TSNamedType (TSNamed nm nt) _ -> case nt of
            TSNPrimType (PS (TSEnum ds) f _) -> do
              guard $ tsnName == nm
              Refl <- vecSame (snd <$> cs) (snd <$> ds)
              guard $ cs == ds
              pure $ f . psSerializer
            TSNFunc _ -> Nothing
          _ -> Nothing
    TSPrimType (PS xi _ xs) -> loopReAssign t0 $ reAssignPrim xs xi

vecSame :: Vec n a -> Vec m a -> Maybe (n :~: m)
vecSame = \case
  VNil -> \case
    VNil -> Just Refl
    _    -> Nothing
  _ ::: xs -> \case
    VNil -> Nothing
    _ ::: ys -> (\case Refl -> Refl) <$> vecSame xs ys

-- | Loops on being TSNullable or TSSingle or TSNamedType TSNFunc.
loopReAssign
    :: forall a b k l. ()
    => TSType 'Nat.Z l a
    -> (forall j c. TSType 'Nat.Z j c -> Maybe (a -> Either Text c))
    -> TSType 'Nat.Z k b
    -> Maybe (a -> Either Text b)
loopReAssign z f = go
  where
    go :: TSType 'Nat.Z j c -> Maybe (a -> Either Text c)
    go = \case
    -- TODO: need to loop
      TSNullable t -> go (unNullable t)
      TSSingle t -> go t
      TSNamedType (TSNamed _ (TSNFunc tf)) ps -> go (tsApply tf ps)
      TSUnion ts -> fmap runStar . getCompose $ postAltT (Compose . fmap Star . withTSType_ go) ts
      TSPrimType (PS TSAny g _) -> Just $ g . typeToValue z
      TSPrimType (PS TSUnknown g _) -> Just $ g . typeToValue z
      t -> f t

reAssignTuple
    :: Ap (Pre a (TSType_ 'Nat.Z)) c
    -> Ap (Pre b (TSType_ 'Nat.Z)) d
    -> Maybe (a -> Either Text d)
reAssignTuple = \case
    Pure _ -> \case
      Pure y -> Just $ \_ -> Right y
      Ap _ _ -> Nothing
    Ap (f :>$<: TSType_ x) xs -> \case
      Pure _ -> Nothing
      Ap (_ :>$<: TSType_ y) ys -> do
        rxs <- reAssign x y
        rys <- reAssignTuple xs ys
        Just $ \r -> rys r <*> rxs (f r)

splitAp :: forall f b. Ap f b -> [Some f]
splitAp = go
  where
    go :: Ap f c -> [Some f]
    go = \case
      Pure _ -> []
      Ap x xs -> Some x : go xs

reAssignIsObj :: TSType 'Nat.Z 'IsObj a -> TSType 'Nat.Z k b -> Maybe (a -> Either Text b)
reAssignIsObj x = \case
    TSArray _  -> Nothing
    TSNullable t -> reAssignIsObj x (unNullable t)
    TSTuple _ -> Nothing
    TSSingle y -> reAssignIsObj x y
    TSObject y -> assembleIsObj mp (TSObject y)
    TSUnion  _ -> undefined -- TODO: do the whole thing
    TSNamedType TSNamed{..} ps -> case tsnType of
      TSNFunc tf -> reAssignIsObj x (tsApply tf ps)
      TSNPrimType _ -> Nothing
    TSIntersection y -> assembleIsObj mp (TSIntersection y)
    TSPrimType _ -> Nothing
  where
    mp = isObjKeyVals x

isObjKeyVals
    :: TSType p 'IsObj a
    -> Map Text (Some (Pre a (TSType_ p)))
isObjKeyVals = \case
    TSObject ts -> splitKeyVal ts
    TSIntersection (PreT ts) -> hfoldMap
      (\(f :>$<: t) -> isObjKeyVals t <&> \case Some p -> Some (mapPre f p))
      ts
    TSNamedType _ _ -> undefined

assembleIsObj
    :: forall a b. ()
    => Map Text (Some (Pre a (TSType_ 'Nat.Z)))
    -> TSType 'Nat.Z 'IsObj b
    -> Maybe (a -> Either Text b)
assembleIsObj mp = \case
    TSObject ts -> assembleKeyVal mp ts
    TSIntersection ts -> fmap runReaderT . getCompose $
        interpret (Compose . fmap ReaderT . assembleIsObj mp) ts
    TSNamedType _ _ -> undefined

splitKeyVal :: TSKeyVal p a -> Map Text (Some (Pre a (TSType_ p)))
splitKeyVal (PreT p) = M.fromList $ splitAp p <&> \case
    Some (q :>$<: ObjMember{..}) ->
      ( objMemberKey
      , case objMemberVal of
          L1 z -> Some $ q :>$<: z
          R1 (ILan f g (TSType_ w)) -> Some $
            q :>$<: TSType_ (TSNullable (ILan f g w))
      )

assembleKeyVal
    :: forall a b. ()
    => Map Text (Some (Pre a (TSType_ 'Nat.Z)))
    -> TSKeyVal 'Nat.Z b
    -> Maybe (a -> Either Text b)
assembleKeyVal mp (PreT p) = go p
  where
    go :: Ap (Pre d (ObjMember (TSType_ 'Nat.Z))) c -> Maybe (a -> Either Text c)
    go = \case
      Pure x -> Just $ \_ -> Right x
      Ap (_ :>$<: ObjMember{..}) xs -> do
        Some (q :>$<: TSType_ u) <- M.lookup objMemberKey mp
        -- if the original is Non-Nullable, we can assign it to anything
        -- if the original is Nullable, we can only assign it to Nullable
        let objVal = case objMemberVal of
              L1 t                      -> t
              R1 (ILan g h (TSType_ t)) -> TSType_ $ TSNullable (ILan g h t)
        (`withTSType_` objVal) $ \t -> do
          rx  <- reAssign u t
          rxs <- go xs
          pure $ \r -> rxs r <*> rx (q r)
