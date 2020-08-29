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
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedLabels           #-}
{-# LANGUAGE OverloadedLabels           #-}
{-# LANGUAGE OverloadedStrings          #-}
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

module Typescript.Json.Core (
    TSPrim(..)
  , EnumLit(..)
  , TSType(..)
  , TSType_(..)
  , KeyChain(..)
  , Intersections(..)
  -- , mapName
  -- * prettyprint
  , ppEnumLit
  , ppPrim
  , ppType
  , ppTypeWith
  , ppTypeFWith
  -- , typeExports
  -- * to value
  , enumLitToValue
  , primToValue
  , typeToValue
  -- * parse
  , parseEnumLit
  , parsePrim
  , parseType
  -- * utility func
  , injectKC
  , keyChainKeys
  , type (++)
  -- * utility types
  , Key(..)
  , Keyed(..)
  , PS(..)
  , Elem(..)
  , ILan(..)
  , ilan
  ) where

import           Control.Applicative
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Writer
import           Data.Bifunctor
import           Data.Dependent.Sum                        (DSum)
import           Data.Fin                                  (Fin)
import           Data.Foldable
import           Data.Functor
import           Data.Functor.Combinator hiding            (Comp(..))
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Contravariant.Divisible.Free (Dec(..))
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.GADT.Show
import           Data.HFunctor.Route
import           Data.IntMap                               (IntMap)
import           Data.Kind
import           Data.Map                                  (Map)
import           Data.Ord
import           Data.Proxy
import           Data.SOP                                  (NP(..), NS(..), I(..), K(..), (:.:)(..))
import           Data.Scientific                           (Scientific, toBoundedInteger)
import           Data.Some                                 (Some(..), withSome, foldSome, mapSome)
import           Data.Text                                 (Text)
import           Data.Type.Equality
import           Data.Vec.Lazy                             (Vec)
import           Data.Vector                               (Vector)
import           Data.Void
import           GHC.Generics                              (Generic, (:*:)(..))
import           GHC.OverloadedLabels
import           GHC.TypeLits
import           Numeric.Natural
import           Unsafe.Coerce
import qualified Data.Aeson                                as A
import qualified Data.Aeson.BetterErrors                   as ABE
import qualified Data.Aeson.Types                          as A
import qualified Data.Bifunctor.Assoc                      as B
import qualified Data.HashMap.Strict                       as HM
import qualified Data.HashSet                              as HS
import qualified Data.Map                                  as M
import qualified Data.SOP                                  as SOP
import qualified Data.SOP.NP                               as NP
import qualified Data.Text                                 as T
import qualified Data.Vec.Lazy                             as Vec
import qualified Data.Vector                               as V
import qualified Prettyprinter                             as PP

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

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
    '[]     ++ bs = bs
    (a':as) ++ bs = a':(as ++ bs)

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


data TSType_ ps n a = forall ks. TSType_ { unTSType_ :: TSType ps ks n a }

withTSType_
    :: (forall ks. TSType ps ks n a -> r)
    -> TSType_ ps n a
    -> r
withTSType_ f (TSType_ t) = f t

mapTSType_
    :: (forall ks. TSType ps ks n a -> TSType us ks m b)
    -> TSType_ ps n a
    -> TSType_ us m b
mapTSType_ f (TSType_ t) = TSType_ (f t)

traverseTSType_
    :: Functor f
    => (forall ks. TSType ps ks n a -> f (TSType ps ks m b))
    -> TSType_ ps n a
    -> f (TSType_ ps m b)
traverseTSType_ f (TSType_ t) = TSType_ <$> f t


data Elem :: [k] -> k -> Type where
    EZ :: Elem (a ': as) a
    ES :: !(Elem as a) -> Elem (b ': as) a

ixNP :: NP f as -> Elem as a -> f a
ixNP = \case
    Nil -> \case {}
    x :* xs -> \case
      EZ   -> x
      ES i -> ixNP xs i


data Key :: Symbol -> Type where
    Key :: KnownSymbol k => Key k

instance KnownSymbol k => IsLabel k (Key k) where
    fromLabel = Key

keyText :: Key k -> Text
keyText k@Key = T.pack (symbolVal k)

data Keyed k f a = Keyed
    { keyedKey  :: Key k
    , keyedItem :: f a
    }
  deriving Functor

instance Contravariant f => Contravariant (Keyed k f) where
    contramap f (Keyed k x) = Keyed k (contramap f x)

instance Invariant f => Invariant (Keyed k f) where
    invmap f g (Keyed k x) = Keyed k (invmap f g x)

instance HFunctor (Keyed k) where
    hmap f (Keyed k x) = Keyed k (f x)

instance HTraversable (Keyed k) where
    htraverse f (Keyed k x) = Keyed k <$> f x

instance KnownSymbol k => Inject (Keyed k) where
    inject x = Keyed Key x

instance KnownSymbol k => Interpret (Keyed k) f where
    interpret f (Keyed _ x) = f x

data KeyChain :: [Symbol] -> (Type -> Type) -> Type -> Type where
    KCNil  :: a -> KeyChain '[] f a
    KCCons :: (a -> b -> c)
           -> (c -> (a, b))
           -> (Elem ks k -> Void)
           -> Keyed k (f :+: ILan Maybe f) a
           -> KeyChain ks f b
           -> KeyChain (k ': ks) f c

instance Invariant (KeyChain ks f) where
    invmap f g = \case
      KCNil x -> KCNil (f x)
      KCCons h k e x xs -> KCCons (\r -> f . h r) (k . g) e x xs

instance HFunctor (KeyChain ks) where
    hmap f = \case
      KCNil x -> KCNil x
      KCCons g h n x xs -> KCCons g h n (hmap (hbimap f (hmap f)) x) (hmap f xs)

instance HTraversable (KeyChain ks) where
    htraverse f = \case
      KCNil x -> pure (KCNil x)
      KCCons g h n x xs -> KCCons g h n
        <$> htraverse (\case L1 y -> L1 <$> f y; R1 z -> R1 <$> htraverse f z) x
        <*> htraverse f xs

injectKC :: Key k -> f a -> KeyChain '[k] f a
injectKC k x = KCCons const (,()) (\case {}) (Keyed k (L1 x)) (KCNil ())

instance KnownSymbol k => Inject (KeyChain '[k]) where
    inject = injectKC Key

keyChainKeys
    :: KeyChain ks f a
    -> NP Key ks
keyChainKeys = \case
    KCNil _ -> Nil
    KCCons _ _ _  (Keyed k _) xs -> k :* keyChainKeys xs

runCoKeyChain
    :: forall ks f g. Applicative g
    => (Text -> f ~> g)
    -> (forall x. Text -> f x -> g (Maybe x))
    -> KeyChain ks f ~> g
runCoKeyChain f h = go
  where
    go :: KeyChain js f ~> g
    go = \case
      KCNil x -> pure x
      KCCons  g _ _ (Keyed k x) xs ->
        let runner :: f :+: ILan Maybe f ~> g
            runner = f (keyText k)
                 !*! interpretCoILan (h (keyText k))
        in  liftA2 g (runner x) (go xs)

runContraKeyChain
    :: forall ks f g. Divisible g
    => (Text -> f ~> g)
    -> (forall x. Text -> f x -> g (Maybe x))
    -> KeyChain ks f ~> g
runContraKeyChain f h = go
  where
    go :: KeyChain js f ~> g
    go = \case
      KCNil _ -> conquer
      KCCons _ g _ (Keyed k x) xs ->
        let runner :: f :+: ILan Maybe f ~> g
            runner = f (keyText k)
                 !*! interpretContraILan (h (keyText k))
        in  divide g (runner x) (go xs)

_testChain :: KeyChain '[ "hello", "world" ] Identity (Int, Bool)
_testChain = KCCons (,)   id    (\case {}) (Keyed #hello (L1 $ Identity 10 ))
           . KCCons const (,()) (\case {}) (Keyed #world (L1 $ Identity True))
           $ KCNil  ()

data Intersections :: [Symbol] -> [Symbol] -> Type -> Type -> Type where
    INil  :: a -> Intersections ps '[] n a
    ICons :: (a -> b -> c)
          -> (c -> (a, b))
          -> NP (Not :.: Elem js) ks
          -> TSType ps ('Just ks) n a
          -> Intersections ps js n b
          -> Intersections ps (ks ++ js) n c

instance Invariant (Intersections ps ks n) where
    invmap f g = \case
      INil x -> INil (f x)
      ICons h j ns x xs -> ICons (\r -> f . h r) (j . g) ns x xs

hoistIntersections
    :: (forall ks. TSType ps ('Just ks) n ~> TSType qs ('Just ks) m)
    -> Intersections ps kss n ~> Intersections qs kss m
hoistIntersections f = \case
    INil x -> INil x
    ICons h g ns x xs -> ICons h g ns (f x) (hoistIntersections f xs)

traverseIntersections
    :: Applicative h
    => (forall ks x. TSType ps ('Just ks) n x -> h (TSType qs ('Just ks) m x))
    -> Intersections ps kss n a
    -> h (Intersections qs kss m a)
traverseIntersections f = \case
    INil x -> pure (INil x)
    ICons h g ns x xs -> ICons h g ns <$> f x <*> traverseIntersections f xs


runCoIntersections
    :: forall kss ps n f. Applicative f
    => (forall ks. TSType ps ('Just ks) n ~> f)
    -> Intersections ps kss n ~> f
runCoIntersections f = go
  where
    go :: Intersections ps jss n ~> f
    go = \case
      INil x -> pure x
      ICons g _ _ t ts -> liftA2 g (f t) (go ts)

runContraIntersections
    :: forall kss ps n f. Divisible f
    => (forall ks. TSType ps ('Just ks) n ~> f)
    -> Intersections ps kss n ~> f
runContraIntersections f = go
  where
    go :: Intersections ps jss n ~> f
    go = \case
      INil _           -> conquer
      ICons _ g _ t ts -> divide g (f t) (go ts)

data IsInterface n = NotInterface | IsInterface n
  deriving (Show, Eq, Ord, Functor)

data Param :: Symbol -> Type where
    Param :: KnownSymbol p => Param p

instance KnownSymbol p => IsLabel p (Param p) where
    fromLabel = Param

paramText :: Param p -> Text
paramText p@Param = T.pack (symbolVal p)

textParam :: Text -> (forall p. Param p -> r) -> r
textParam t = case someSymbolVal (T.unpack t) of
    SomeSymbol (Proxy :: Proxy p) -> \f -> f (Param @p)

newtype Fun a b = Fun (a -> b)

data TSType :: [Symbol] -> Maybe [Symbol] -> Type -> Type -> Type where
    TSArray        :: ILan [] (TSType ps ks n) a -> TSType ps 'Nothing n a
    TSTuple        :: PreT Ap (TSType_ ps n) a -> TSType ps 'Nothing n a
    TSObject       :: IsInterface n -> KeyChain ks (TSType_ ps n) a -> TSType ps ('Just ks) n a
    TSUnion        :: PostT Dec (TSType_ ps n) a -> TSType ps 'Nothing n a
    TSNamed        :: n -> TSType ps ks n a -> TSType ps ks n a
    TSApply        :: TSTypeF ps ks n as b -> NP (TSType_ ps n) as -> TSType ps ks n b
    TSVar          :: !(Elem ps p) -> TSType ps ks n a
    -- either we:
    --
    -- 1. do not allow duplicates, in which case we disallow some potential
    --    useful types that people would want to use intersections for in
    --    the first place
    -- 2. allow duplicates, but somehow find a way to make sure 'a' is
    --    Void
    --
    -- #2 seems pretty much impossible without a full impelemntation of the
    -- type system
    TSIntersection :: Intersections ps ks n a -> TSType ps ('Just ks) n a
    TSPrimType     :: PS TSPrim a -> TSType ps 'Nothing n a

    -- Generics
    -- okay, let's think about what kind of interface we actually want
    --
    -- should we be able to actually parse an unapplied generic?
    -- a `Foo<T>`?  like
    --
    -- TSGeneric "Foo" "T" (TSObject NoInterface ("hello" := TSVar IZ, "goodbye" := Number))
    --
    -- what should that be parsed as?
    --
    -- If the final data type is something like
    --
    -- data Foo a = Foo { hello :: a, goodbye :: Int }
    --
    -- it would really only make sense to parse a "Foo a".  never a "Foo".
    -- Since these are all *-kinded types.
    --
    -- If that's the case then how do we want to express Foo a as a typescript type?
    --
    -- ah. we want to be able to document it maybe?  but... this can't be
    -- *.  maybe there should be a TSType2, for * -> * generics types?  how
    -- would that even work?  would we need a full on type system?

data TSTypeF :: [Symbol] -> Maybe [Symbol] -> Type -> [Type] -> Type -> Type where
    TSGeneric
        :: n
        -> NP (K Text) as
        -> (forall rs. NP Param rs -> NP (TSType_ (rs ++ ps) n) as -> TSType (rs ++ ps) ks n b)
        -> TSTypeF ps ks n as b

data Maybe_ :: (k -> Type) -> Maybe k -> Type where
    Nothing_ :: Maybe_ f 'Nothing
    Just_    :: f a -> Maybe_ f ('Just a)

type family CatMaybes (as :: [Maybe k]) :: [k] where
    CatMaybes '[] = '[]
    CatMaybes ('Nothing ': as) = CatMaybes as
    CatMaybes ('Just a  ': as) = a ': CatMaybes as

tsSplit
    :: TSType (p ': ps) ks n a
    -> MaybeF (TSType ps ks n) a
tsSplit = \case
    TSVar EZ     -> MaybeF Nothing
    TSVar (ES e) -> MaybeF $ Just (TSVar e)

tsShift
    :: forall p ps ks n a. ()
    => TSType ps ks n a
    -> TSType (p ': ps) ks n a
tsShift = \case
    TSVar e -> TSVar (ES e)

withSplit
    :: (TSType ps ks n a -> TSType us js m a)
    -> TSType (p ': ps) ks n a
    -> TSType (p ': us) js m a
withSplit f = \case
    TSVar EZ     -> TSVar EZ
    TSVar (ES e) -> tsShift (f (TSVar e))

tsApply
    :: TSTypeF ps ks n as b      -- ^ type function
    -> NP (TSType_ ps n) as         -- ^ thing to apply
    -> TSType ps ks n b
tsApply (TSGeneric _ _ f) t = f Nil t

tsApply1
    :: TSTypeF ps ks n '[a] b      -- ^ type function
    -> TSType ps js n a         -- ^ thing to apply
    -> TSType ps ks n b
tsApply1 (TSGeneric _ p f) t = f Nil (TSType_ t :* Nil)

withParams
    :: NP (K Text) as
    -> (forall bs. NP Param bs -> NP (K (Some (Elem bs))) as -> r)
    -> r
withParams = \case
    Nil -> \f -> f Nil Nil
    K p :* ps -> \f -> textParam p $ \pp ->
      withParams ps $ \pps ees ->
        f (pp :* pps) (K (Some EZ) :* hmap (K . mapSome ES . SOP.unK) ees)

weaken
    :: forall as bs a. ()
    => Elem as a
    -> Elem (as ++ bs) a
weaken = \case
    EZ   -> EZ
    ES e -> ES (weaken @_ @bs e)


tsApplyVar1
    :: TSTypeF ps ks n '[a] b
    -> (forall q. Param q -> TSType (q ': ps) ks n b -> r)
    -> r
tsApplyVar1 (TSGeneric _ (K t :* Nil) g) f = textParam t $ \q ->
    f q (g (q :* Nil) (TSType_ (TSVar EZ) :* Nil))

tsApplyVar
    :: forall ps ks n as b r. ()
    => TSTypeF ps ks n as b
    -> (forall rs. NP Param rs -> TSType (rs ++ ps) ks n b -> r)
    -> r
tsApplyVar (TSGeneric _ ps g) f = withParams ps $ \qs es ->
        f qs (g qs (hmap (\(K (Some i)) -> TSType_ (TSVar (weaken @_ @ps i))) es))

takeNP
    :: forall as bs p q. ()
    => NP p as
    -> NP q (as ++ bs)
    -> (NP (p :*: q) as, NP q bs)
takeNP = \case
    Nil -> (Nil,)
    x :* xs -> \case
      y :* ys -> first ((x :*: y) :*) (takeNP xs ys)


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

instance Invariant (TSType ps ks n) where
    invmap = undefined

imapNP
    :: (forall a. Elem as a -> f a -> g a)
    -> NP f as
    -> NP g as
imapNP f = \case
    Nil -> Nil
    x :* xs -> f EZ x :* imapNP (f . ES) xs

tsGeneric1
    :: n
    -> Text
    -> (forall r. Param r -> TSType_ (r ': ps) n a -> TSType (r ': ps) ks n b)
    -> TSTypeF ps ks n '[a] b
tsGeneric1 n p f = TSGeneric n (K p :* Nil) (\(mp :* Nil) (t :* Nil) -> f mp t)

tsMaybeBool :: TSType '[] 'Nothing Text (Maybe Bool)
tsMaybeBool = tsApply1 tsMaybe (TSPrimType (PS TSBoolean Right id))

tsMaybe :: TSTypeF '[] 'Nothing Text '[a] (Maybe a)
tsMaybe = tsGeneric1 "Maybe" "T" $ \_ (TSType_ t) ->
    TSUnion . PostT $
        decide (maybe (Left ()) Right)
          (injectPost (const Nothing) (TSType_ nothin))
          (injectPost Just (TSType_ (justin t)))


nothin :: TSType ps ('Just '["tag"]) n ()
nothin = TSObject NotInterface $
    KCCons const (,()) (\case {}) (Keyed (Key @"tag") (L1 (TSType_ $ TSPrimType primTag)))
      $ KCNil ()
  where
    primTag = PS (TSStringLit "Nothing") Right id

justin :: TSType ps ks n a -> TSType ps ('Just '["tag", "contents"]) n a
justin t = TSObject NotInterface $
    KCCons (const id) ((),) (\case {}) (Keyed (Key @"tag") (L1 (TSType_ $ TSPrimType primTag)))
      . KCCons const (,()) (\case {}) (Keyed (Key @"contents") (L1 (TSType_ t)))
      $ KCNil ()
  where
    primTag = PS (TSStringLit "Just") Right id

-- mapName :: forall ps ks n m. (n -> m) -> TSType ps ks n ~> TSType ps ks m
-- mapName f = go
--   where
--     go :: TSType us js n ~> TSType us js m
--     go = \case
--       TSArray l         -> TSArray (hmap go l)
--       TSTuple ts        -> TSTuple (hmap (mapTSType_ go) ts)
--       TSObject ii ts    -> TSObject (fmap f ii) (hmap (mapTSType_ go) ts)
--       TSUnion ts        -> TSUnion (hmap (mapTSType_ go) ts)
--       TSNamed n t       -> TSNamed (f n) (go t)
--       -- TSApply (TSGeneric n p g) t -> TSApply (TSGeneric (f n) p (\q -> _ . g q . _)) (hmap (mapTSType_ go) t)
--       -- TSGeneric n p t   -> TSGeneric (f n) p (go t)
--       TSVar i           -> TSVar i
--       TSIntersection ts -> TSIntersection (hoistIntersections go ts)
--       TSPrimType t      -> TSPrimType t


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
          [ PP.pretty e PP.<+> ppEnumLit x
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
    :: PP.Pretty n
    => NP Param ps
    -> TSType ps ks n a
    -> PP.Doc x
ppType = ppTypeWith PP.pretty

ppTypeWith
    :: forall ps ks n a x. ()
    => (n -> PP.Doc x)
    -> NP Param ps
    -> TSType ps ks n a
    -> PP.Doc x
ppTypeWith f = go
  where
    go :: NP Param qs -> TSType qs js n b -> PP.Doc x
    go ps = \case
      TSArray t   -> getConst (interpretILan (Const . go ps) t) <> "[]"
      TSTuple ts  -> PP.encloseSep "[" "]" ", " (icollect (withTSType_ (go ps)) ts)
      TSObject NotInterface ts -> PP.encloseSep "{" "}" "," . getConst $
        runCoKeyChain
          (\k x -> Const [PP.pretty k <> ":" PP.<+> withTSType_ (go ps) x])
          (\k x -> Const [PP.pretty k <> "?:" PP.<+> withTSType_ (go ps) x])
          ts
      TSObject (IsInterface n) _ -> f n
      TSUnion ts  -> PP.encloseSep "" "" " | " (icollect (withTSType_ (go ps)) ts)
      TSNamed n _ -> f n
      -- this is the benefit of delaying application
      TSApply (TSGeneric n _ _) xs -> f n <> PP.encloseSep "<" ">" ","
        (htoList (withTSType_ (go ps)) xs)
      TSVar i -> PP.pretty (paramText (ps `ixNP` i))
      TSIntersection ts  -> PP.encloseSep "" "" " & " . getConst $
        runCoIntersections (\x -> Const [go ps x]) ts
      TSPrimType PS{..} -> ppPrim psItem

ppTypeFWith
    :: forall ps ks n a b x. ()
    => (n -> PP.Doc x)
    -> TSTypeF ps ks n a b
    -> PP.Doc x
ppTypeFWith f tf@(TSGeneric n rs _) =
    f n PP.<> PP.encloseSep "<" ">" "," (htoList (PP.pretty . SOP.unK) rs)

typeExports
    :: (Ord n, PP.Pretty n)
    => NP Param ps
    -> Maybe (IsInterface (), n)    -- ^ top-level name and interface, if meant to be included
    -> TSType ps ks n a
    -> PP.Doc x
typeExports ps iin0 ts =
      ppMap
    . maybe id (`M.insert` (params0, ppType ps t0)) iin0
    $ tmap0
  where
    ((params0, t0), tmap0) = flattenType (\qs -> ppType (qs `appendNP` ps)) ts

-- meh i can't really do this without extensive testing
-- typeFExports
--     :: (Ord n, PP.Pretty n)
--     => NP Param ps
--     -> TSTypeF ps ks n a b
--     -> PP.Doc x
-- typeFExports ps tf@(TSGeneric n gs _) = tsApplyVar tf $ \rs ts ->
--     let ((params0, t0), tmap0) = flattenType (\qs -> ppType (qs `appendNP` (rs `appendNP` ps))) ts
--     in  ppMap
--           . M.insert (NotInterface(), n) (htoList _ p, ppType (rs `appendNP` ps) t0)
--           -- . maybe id (`M.insert` (params0, ppType (rs `appendNP` ps) t0)) iin0
--           -- . maybe id (`M.insert` (params0, ppType (rs `appendNP` ps) t0)) iin0
--           $ tmap0

ppMap
    :: PP.Pretty n
    => Map (IsInterface (), n) ([Text], PP.Doc x)
    -> PP.Doc x
ppMap mp = PP.vcat
    [ PP.vsep [
        "export"
      , iiString ii
      , PP.pretty n <> PP.encloseSep "<" ">" "," (PP.pretty <$> params)
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
    :: Ord n
    => (forall qs js b. NP Param qs -> TSType (qs ++ ps) js Void b -> r)
    -> TSType ps ks n a
    -> (([Text], TSType ps ks Void a), Map (IsInterface (), n) ([Text], r))
flattenType f t = runState (flattenType_ f t) M.empty

flattenType_
    :: forall ps ks n a r. Ord n
    => (forall qs js b. NP Param qs -> TSType (qs ++ ps) js Void b -> r)
    -> TSType ps ks n a
    -> State (Map (IsInterface (), n) ([Text], r)) ([Text], TSType ps ks Void a)
flattenType_ f = go Nil
  where
    go  :: forall qs js b. ()
        => NP Param qs
        -> TSType (qs ++ ps) js n b
        -> State (Map (IsInterface (), n) ([Text], r)) ([Text], TSType (qs ++ ps) js Void b)
    go qs = \case
      TSArray t  -> ([],) . TSArray <$> htraverse (fmap snd . go qs) t
      TSTuple ts -> ([],) . TSTuple <$> htraverse (traverseTSType_ (fmap snd . go qs)) ts
      TSObject ii ts -> do
        res <- TSObject NotInterface <$> htraverse (traverseTSType_ (fmap snd . go qs)) ts
        case ii of
          NotInterface  -> pure ([], res)
          IsInterface n -> do
            modify $ M.insert (IsInterface(), n) ([], f qs res)
            pure ([], res)
      TSUnion ts -> ([],) . TSUnion <$> htraverse (traverseTSType_ (fmap snd . go qs)) ts
      TSApply tf@(TSGeneric n ps _) t -> do
        tsApplyVar @_ @_ @_ @_ @_ @(State _ ()) tf $ \(rs :: NP Param rs) tv -> case assocConcat @rs @qs @ps rs of
          Refl -> do
            (_, res) <- go (rs `appendNP` qs) tv
            modify $ M.insert (NotInterface, n)
              (htoList SOP.unK ps, f (rs `appendNP` qs) res)
        -- is this right?
        gets $ evalState (go qs (tsApply tf t))
      TSNamed n t -> do
        (_, res) <- go qs t
        modify $ M.insert (NotInterface, n) ([], f qs res)
        pure ([], res)
      TSVar i -> pure ([], TSVar i)
      TSIntersection ts -> ([],) . TSIntersection <$> traverseIntersections (fmap snd . go qs) ts
      TSPrimType p -> pure ([], TSPrimType p)

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

objTypeToValue :: TSType '[] ('Just ks) n a -> a -> [A.Pair]
objTypeToValue = \case
    TSObject     _ ts -> getOp $
      runContraKeyChain
        (\k t -> Op           $ \x -> [k A..= withTSType_ typeToValue t x])
        (\k t -> Op . foldMap $ \x -> [k A..= withTSType_ typeToValue t x])
        ts
    TSIntersection ts -> getOp (runContraIntersections (Op . objTypeToValue) ts)
    TSNamed      _   t -> objTypeToValue t
    TSApply      f   t -> objTypeToValue (tsApply f t)

typeToValue
    :: TSType '[] ks n a -> a -> A.Value
typeToValue = \case
    TSArray ts        -> A.Array
                       . V.fromList
                       . getOp (interpretILan (\t -> Op (map (typeToValue t))) ts)
    TSTuple ts        -> A.Array
                       . V.fromList
                       . getOp (preDivisibleT (\t -> Op $ \x -> [withTSType_ typeToValue t x]) ts)
    TSObject ii ts    -> A.object . objTypeToValue (TSObject ii ts)
    TSUnion ts        -> iapply (withTSType_ typeToValue) ts
    TSNamed _ t       -> typeToValue t
    TSApply f t       -> typeToValue (tsApply f t)
    TSIntersection ts -> A.object . getOp (runContraIntersections (Op . objTypeToValue) ts)
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
    :: PP.Pretty n
    => TSType '[] ks n a
    -> Parse a
parseType = \case
    TSArray ts -> unwrapFunctor $ interpretILan (WrapFunctor . ABE.eachInArray . parseType) ts
    TSTuple ts -> do
      (res, n) <- flip runStateT 0 $ (`interpret` ts) $ \t -> StateT $ \i ->
        (,i+1) <$> ABE.nth i (withTSType_ parseType t)
      ABE.withArray $ \xs ->
        if V.length xs > n
          then Left $ PEExtraTuple n (V.length xs)
          else pure res
    TSObject _ ts -> runCoKeyChain
        (\k -> ABE.key    k . withTSType_ parseType)
        (\k -> ABE.keyMay k . withTSType_ parseType)
        ts
    TSUnion ts ->
      let us = icollect (withTSType_ (ppType Nil)) ts
      in  foldr @[] (ABE.<|>) (ABE.throwCustomError (PENotInUnion us)) $
            icollect (interpretPost (withTSType_ parseType)) (unPostT ts)
    TSNamed _ t -> parseType t
    TSApply t f -> parseType (tsApply t f)
    TSIntersection ts -> runCoIntersections parseType ts
    TSPrimType PS{..} -> either (ABE.throwCustomError . PEPrimitive (Some psItem)) pure . psParser
                     =<< parsePrim psItem

appendNP :: NP f as -> NP f bs -> NP f (as ++ bs)
appendNP = \case
    Nil -> id
    x :* xs -> (x :*) . appendNP xs

