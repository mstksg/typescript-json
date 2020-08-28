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
  , mapName
  -- * prettyprint
  , ppEnumLit
  , ppPrim
  , ppType
  , ppTypeWith
  -- , typeExports
  -- * to value
  , enumLitToValue
  , primToValue
  , typeToValue
  -- * parse
  , parseEnumLit
  , parsePrim
  -- , parseType
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
import           Numeric.Natural
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
import           Data.Some                                 (Some(..), withSome, foldSome)
import           Data.Text                                 (Text)
import           Data.Type.Equality
import           Data.Vec.Lazy                             (Vec)
import           Data.Vector                               (Vector)
import           Data.Void
import           GHC.Generics                              (Generic, (:*:)(..))
import           GHC.OverloadedLabels
import           GHC.TypeLits
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

newtype Fun a b = Fun (a -> b)

data TSType :: [Symbol] -> Maybe [Symbol] -> Type -> Type -> Type where
    TSArray        :: ILan [] (TSType ps ks n) a -> TSType ps 'Nothing n a
    TSTuple        :: PreT Ap (TSType_ ps n) a -> TSType ps 'Nothing n a
    TSObject       :: IsInterface n -> KeyChain ks (TSType_ ps n) a -> TSType ps ('Just ks) n a
    TSUnion        :: PostT Dec (TSType_ ps n) a -> TSType ps 'Nothing n a
    TSNamed        :: n -> TSType ps ks n a -> TSType ps ks n a
    -- TSApply        :: TSType ps ks n (Fun p a) -> TSType ps ks n p -> TSType ps ks n a
    TSApply        :: TSTypeF ps n f -> TSType ps ks n a -> TSType ps ks n (f a)
    -- this is a problem: what should the 'a' be?
    TSVar          :: Elem ps p -> TSType ps ks n (Param p)
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

type family SubParam p a b where
    SubParam p (Param p) b = b
    SubParam p a         b = a

substitute
    :: TSType (p ': ps) ks n a
    -> TSType ps js n b
    -> TSType_ ps n (SubParam p a b)
substitute = \case
    -- TSTuple ts -> \x -> TSTuple $ hmap (mapTSType_ (`substitute` x)) ts
    TSVar EZ -> TSType_
    -- TSVar          :: Elem ps p -> TSType ps ks n (Param p)
    -- TSTuple        :: PreT Ap (TSType_ ps n) a -> TSType ps 'Nothing n a
    -- TSApply _ _ ->

    -- TSApply        :: Functor f => TSTypeF ps n f -> TSType ps ks n a -> TSType ps ks n (f a)

data TSTypeF :: [Symbol] -> Type -> (Type -> Type) -> Type where
    TSGeneric :: n
              -> Param p
              -> TSType (p ': ps) ks n (f (Param p))
              -> TSTypeF ps n f

tsMaybeInt :: TSType '[] 'Nothing Text (Maybe Bool)
tsMaybeInt = TSApply tsMaybe (TSPrimType (PS TSBoolean Right id))

tsMaybe :: TSTypeF '[] Text Maybe
tsMaybe = TSGeneric "Maybe" (Param @"T") $
    TSUnion . PostT $ 
        decide (maybe (Left ()) Right)
          (injectPost (const Nothing) (TSType_ nothin))
          (injectPost Just (TSType_ justin))


nothin :: TSType ps ('Just '["tag"]) n ()
nothin = TSObject NotInterface $
    KCCons const (,()) (\case {}) (Keyed (Key @"tag") (L1 (TSType_ $ TSPrimType primTag)))
      $ KCNil ()
  where
    primTag = PS (TSStringLit "Nothing") Right id

justin :: TSType ("T" ': ps) ('Just '["tag", "contents"]) n (Param "T")
justin = TSObject NotInterface $
    KCCons (const id) ((),) (\case {}) (Keyed (Key @"tag") (L1 (TSType_ $ TSPrimType primTag)))
      . KCCons const (,()) (\case {}) (Keyed (Key @"contents") (L1 (TSType_ $ TSVar EZ)))
      $ KCNil ()
  where
    primTag = PS (TSStringLit "Just") Right id

-- justin :: TSType ("T" ': ps) 'Nothing n (Maybe a)
-- justin = TSPrimType (PS (TSStringLit "Nothing") (const (Right Nothing)) (const ()))
        
    -- TSStringLit  :: Text -> TSPrim ()

-- injectKC :: Key k -> f a -> KeyChain '[k] f a
-- injectKC k x = KCCons const (,()) (\case {}) (Keyed k (L1 x)) (KCNil ())

    -- KCCons :: (a -> b -> c)
    --        -> (c -> (a, b))
    --        -> (Elem ks k -> Void)
    --        -> Keyed k (f :+: ILan Maybe f) a
    --        -> KeyChain ks f b
    --        -> KeyChain (k ': ks) f c

            -- KCCons  _ _ _
      -- PostT $

    ---- okay, let's think about what kind of interface we actually want
    ----
    ---- should we be able to actually parse an unapplied generic?
    ---- a `Foo<T>`?  like
    ----
    ---- TSGeneric "Foo" "T" (TSObject NoInterface ("hello" := TSVar IZ, "goodbye" := Number))
    ----
    ---- what should that be parsed as?
    ----
    ---- If the final data type is something like
    ----
    ---- data Foo a = Foo { hello :: a, goodbye :: Int }
    ----
    ---- it would really only make sense to parse a "Foo a".  never a "Foo".
    ---- Since these are all *-kinded types.
    ----
    ---- If that's the case then how do we want to express Foo a as a typescript type?
    ----
    ---- ah. we want to be able to document it maybe?  but... this can't be
    ---- *.  maybe there should be a TSType2, for * -> * generics types?  how
    ---- would that even work?  would we need a full on type system?
    --TSGeneric      :: n -> Text -> TSType (p ': ps) ks n a -> TSType ps ks n (Fun p a)


mapName :: forall ps ks n m. (n -> m) -> TSType ps ks n ~> TSType ps ks m
mapName f = go
  where
    go :: TSType us js n ~> TSType us js m
    go = \case
      TSArray l         -> TSArray (hmap go l)
      TSTuple ts        -> TSTuple (hmap (mapTSType_ go) ts)
      TSObject ii ts    -> TSObject (fmap f ii) (hmap (mapTSType_ go) ts)
      TSUnion ts        -> TSUnion (hmap (mapTSType_ go) ts)
      TSNamed n t       -> TSNamed (f n) (go t)
      -- TSGeneric n p t   -> TSGeneric (f n) p (go t)
      -- TSVar i           -> TSVar i
      TSIntersection ts -> TSIntersection (hoistIntersections go ts)
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
    => NP (K Text) ps
    -> TSType ps ks n a
    -> PP.Doc x
ppType = ppTypeWith PP.pretty

ppTypeWith
    :: forall ps ks n a x. ()
    => (n -> PP.Doc x)
    -> NP (K Text) ps
    -> TSType ps ks n a
    -> PP.Doc x
ppTypeWith f = go
  where
    go :: NP (K Text) qs -> TSType qs js n b -> PP.Doc x
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
      TSNamed n t -> f n
      -- TSGeneric n p _ -> f n PP.<+> ("<" <> PP.pretty p <> ">")
      -- TSVar i -> PP.pretty (SOP.unK (ps `ixNP` i))
      TSIntersection ts  -> PP.encloseSep "" "" " & " . getConst $
        runCoIntersections (\x -> Const [go ps x]) ts
      TSPrimType PS{..} -> ppPrim psItem

-- typeExports
--     :: (Ord n, PP.Pretty n)
--     => Maybe (IsInterface (), n)    -- ^ top-level name and interface, if meant to be included
--     -> TSType ks n a
--     -> PP.Doc x
-- typeExports iin0 ts = PP.vcat
--     [ PP.vsep [
--         "export"
--       , iiString ii
--       , PP.pretty n
--       , "="
--       , ppType t
--       ]
--     | ((ii, n), Some (TSType_ t)) <- M.toList tmap
--     ]
--   where
--     (t0, tmap0) = flattenType ts
--     tmap = maybe id (`M.insert` Some (TSType_ t0)) iin0 tmap0
--     iiString = \case
--       NotInterface  -> "type"
--       IsInterface _ -> "interface"

-- -- | Pull out all of the named types to be top-level type declarations, and
-- -- have create a map of all of those declarations.
-- flattenType
--     :: Ord n
--     => TSType ks n a
--     -> (TSType ks Void a, Map (IsInterface (), n) (Some (TSType_ Void)))
-- flattenType t = runState (flattenType_ t) M.empty

-- flattenType_
--     :: Ord n
--     => TSType ks n a
--     -> State (Map (IsInterface (), n) (Some (TSType_ Void))) (TSType ks Void a)
-- flattenType_ = \case
--     TSArray t  -> TSArray <$> htraverse flattenType_ t
--     TSTuple ts -> TSTuple <$> htraverse (traverseTSType_ flattenType_) ts
--     TSObject ii ts -> do
--       res <- TSObject NotInterface <$> htraverse (traverseTSType_ flattenType_) ts
--       case ii of
--         NotInterface  -> pure res
--         IsInterface n -> do
--           modify $ M.insert (IsInterface(), n) (Some (TSType_ res))
--           pure res
--     TSUnion ts -> TSUnion <$> htraverse (traverseTSType_ flattenType_) ts
--     TSNamed n t -> do
--       res <- flattenType_ t
--       modify $ M.insert (NotInterface, n) (Some (TSType_ res))
--       pure res
--     TSIntersection ts -> TSIntersection <$> traverseIntersections flattenType_ ts
--     TSPrimType p -> pure $ TSPrimType p

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

objTypeToValue :: TSType ps ('Just ks) n a -> a -> [A.Pair]
objTypeToValue = \case
    TSObject     _ ts -> getOp $
      runContraKeyChain
        (\k t -> Op           $ \x -> [k A..= withTSType_ typeToValue t x])
        (\k t -> Op . foldMap $ \x -> [k A..= withTSType_ typeToValue t x])
        ts
    TSIntersection ts -> getOp (runContraIntersections (Op . objTypeToValue) ts)
    TSNamed      _   t -> objTypeToValue t
    -- TSGeneric    _ _ t -> objTypeToValue t
    -- TSVar        i     -> undefined

typeToValue
    :: TSType ps ks n a -> a -> A.Value
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
    -- TSGeneric _ _ t   -> typeToValue t
    -- TSVar     i       -> undefined
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

-- newtype ToParser a = ToParser { runToParser :: forall ps ks n a. TSType ps ks n a -> ABE.Parse ParseErr a }
type Parse = ABE.ParseT ParseErr Identity
-- newtype ParseWithEnv ps a = ParseWithEnv { runParseWithEnv :: NP Parse ps -> Parse a }
--   deriving (Functor, Applicative, Monad) via ReaderT (NP Parse ps) Parse

-- parseType
--     :: PP.Pretty n
--     => TSType ps ks n a
--     -> ParseWithEnv ps a
-- parseType = \case
--     TSGeneric _ p t -> ParseWithEnv $ \ps -> do
--       res <- runParseWithEnv (parseType t) _
--       pure $ _ res
--       -- parseT

parseType
    :: PP.Pretty n
    => NP (K (Some Parse)) ps
    -> TSType ps ks n a
    -> Parse a
parseType ps = \case
    TSArray ts -> unwrapFunctor $ interpretILan (WrapFunctor . ABE.eachInArray . parseType ps) ts
    TSTuple ts -> do
      (res, n) <- flip runStateT 0 $ (`interpret` ts) $ \t -> StateT $ \i ->
        (,i+1) <$> ABE.nth i (withTSType_ (parseType ps) t)
      ABE.withArray $ \xs ->
        if V.length xs > n
          then Left $ PEExtraTuple n (V.length xs)
          else pure res
    TSObject _ ts -> runCoKeyChain
        (\k -> ABE.key    k . withTSType_ (parseType ps))
        (\k -> ABE.keyMay k . withTSType_ (parseType ps))
        ts
    TSUnion ts -> undefined
      -- let us = icollect (withTSType_ (ppType ps)) ts
      -- -- let us = icollect (withTSType_ (ppType (hmap (\(p :*: _) -> p) ps))) ts
      -- in  foldr @[] (ABE.<|>) (ABE.throwCustomError (PENotInUnion us)) $
      --       icollect (interpretPost (withTSType_ (parseType ps))) (unPostT ts)
    TSNamed _ t -> parseType ps t
    -- TSApply (TSGeneric _ p tf) tx -> parseType (K (Some (parseType ps tx)) :* ps) tf

    -- TSApply        :: TSTypeF ps n f -> TSType ps ks n a -> TSType ps ks n (f a)
-- data TSTypeF :: [Symbol] -> Type -> (Type -> Type) -> Type where
--     TSGeneric :: n -> Param p -> ILan f (TSType (p ': ps) ks n) a -> TSTypeF ps n f

    -- TSGeneric _ p t -> do
    --   res <- parseType (K p :* ps) t
    --   Fun <$> _ res
    -- TSApply tf tx -> do
    --   Fun f <- parseType ps tf
    --   x <- parseType ps tx
    --   pure $ f x
    -- -- TSGeneric _ p t -> parseType ((K p :*: undefined) :* ps) t
    -- TSVar     i     -> undefined
    -- (\(_ :*: p) -> p) (ps `ixNP` i)
    TSVar     i     -> undefined -- free variable? _ (ps `ixNP` i)
    -- (\(_ :*: p) -> p)
    TSIntersection ts -> runCoIntersections (parseType ps) ts
    TSPrimType PS{..} -> either (ABE.throwCustomError . PEPrimitive (Some psItem)) pure . psParser
                     =<< parsePrim psItem

-- parseType
--     :: PP.Pretty n
--     => TSType ps ks n a
--     -> (Parse :.: (->) (NP Parse ps)) a
-- parseType = \case
--     -- TSArray ts -> unwrapFunctor $ interpretILan (WrapFunctor . _ ABE.eachInArray . parseType) ts
--     -- TSTuple ts -> do
--     --   (res, n) <- flip runStateT 0 $ (`interpret` ts) $ \t -> StateT $ \i ->
--     --     (,i+1) <$> ABE.nth i (withTSType_ (parseType ps) t)
--     --   ABE.withArray $ \xs ->
--     --     if V.length xs > n
--     --       then Left $ PEExtraTuple n (V.length xs)
--     --       else pure res
--     -- TSObject _ ts -> runCoKeyChain
--     --     (\k -> ABE.key    k . withTSType_ (parseType ps))
--     --     (\k -> ABE.keyMay k . withTSType_ (parseType ps))
--     --     ts
--     -- TSUnion ts ->
--     --   let us = icollect (withTSType_ (ppType (hmap (\(p :*: _) -> p) ps))) ts
--     --   in  foldr @[] (ABE.<|>) (ABE.throwCustomError (PENotInUnion us)) $
--     --         icollect (interpretPost (withTSType_ (parseType ps))) (unPostT ts)
--     -- TSNamed _ t -> parseType ps t
--     TSGeneric _ p t -> SOP.Comp $ do
--       x <- SOP.unComp $ parseType t
--       _ $ x _
--     -- ((K p :*: _) :* ps) t
--     -- TSVar     i     -> (\(_ :*: p) -> p) (ps `ixNP` i)
--     -- TSIntersection ts -> runCoIntersections (parseType ps) ts
--     -- TSPrimType PS{..} -> either (ABE.throwCustomError . PEPrimitive (Some psItem)) pure . psParser
--     --                  =<< parsePrim psItem
