{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Typescript.Types where

import           Control.Applicative
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Dependent.Sum                        (DSum)
import           Data.Fin                                  (Fin)
import           Data.Foldable
import           Data.Functor.Combinator hiding            (Comp(..))
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Contravariant.Divisible.Free (Dec(..))
import           Data.Functor.Identity
import           Data.Functor.Invariant
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

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
    '[]     ++ bs = bs
    (a':as) ++ bs = a':(as ++ bs)

type family Concat (as :: [[k]]) :: [k] where
    Concat '[] = '[]
    Concat (a ': as) = a ++ Concat as

data ListOf f a = forall x. ListOf
    (f x)
    (a -> (forall r. (x -> r -> r) -> r -> r))
    ((forall r. (x -> r -> r) -> r -> r) -> a)

instance Invariant (ListOf f) where
    invmap f g (ListOf x toBuild fromBuild) =
      ListOf x (\xs -> toBuild (g xs)) (\h -> f (fromBuild h))

listOf :: f a -> ListOf f [a]
listOf x = ListOf x
        (\xs cons nil -> foldr cons nil xs)
        (\f -> f (:) [])

instance HFunctor ListOf where
    hmap f (ListOf x g h) = ListOf (f x) g h

interpretListOf
    :: Invariant g
    => (forall x. f x -> g [x])
    -> ListOf f a
    -> g a
interpretListOf f (ListOf x g h) = invmap
    (\xs -> h (\cons nil -> foldr cons nil xs))
    (\y -> g y (:) [])
    (f x)

data TSType_ n a = forall ks. TSType_ { unTSType_ :: TSType ks n a }

withTSType_
    :: (forall ks. TSType ks n a -> r)
    -> TSType_ n a
    -> r
withTSType_ f (TSType_ t) = f t

data Elem :: [k] -> k -> Type where
    EZ :: Elem (a ': as) a
    ES :: !(Elem as a) -> Elem (b ': as) a

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

data KeyChain :: [Symbol] -> (Type -> Type) -> Type -> Type where
    KCNil  :: a -> KeyChain '[] f a
    KCCons :: (a -> b -> c)
           -> (c -> (a, b))
           -> (Elem ks k -> Void)
           -> Keyed k f a
           -> KeyChain ks f b
           -> KeyChain (k ': ks) f c

instance Invariant (KeyChain ks f) where
    invmap f g = \case
      KCNil x -> KCNil (f x)
      KCCons h k e x xs -> KCCons (\r -> f . h r) (k . g) e x xs

instance HFunctor (KeyChain ks) where
    hmap f = \case
      KCNil x -> KCNil x
      KCCons g h n (Keyed k x) xs -> KCCons g h n (Keyed k (f x)) (hmap f xs)

injectKC :: Key k -> f a -> KeyChain '[k] f a
injectKC k x = KCCons const (,()) (\case {}) (Keyed k x) (KCNil ())

instance KnownSymbol k => Inject (KeyChain '[k]) where
    inject = injectKC Key

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

kcCons
    :: KnownNotElem ks k
    => Key k
    -> (a -> b -> c)
    -> (c -> (a, b))
    -> f a
    -> KeyChain ks f b
    -> KeyChain (k ': ks) f c
kcCons k f g x = KCCons f g knownNotElem (Keyed k x)

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

runCoKeyChain
    :: forall ks f g. Applicative g
    => (Text -> f ~> g)
    -> KeyChain ks f ~> g
runCoKeyChain f = go
  where
    go :: KeyChain js f ~> g
    go = \case
      KCNil x -> pure x
      KCCons g _ _ (Keyed k x) xs -> liftA2 g (f (keyText k) x) (go xs)

runContraKeyChain
    :: forall ks f g. Divisible g
    => (Text -> f ~> g)
    -> KeyChain ks f ~> g
runContraKeyChain f = go
  where
    go :: KeyChain js f ~> g
    go = \case
      KCNil _ -> conquer
      KCCons _ g _ (Keyed k x) xs -> divide g (f (keyText k) x) (go xs)

testChain :: KeyChain '[ "hello", "world" ] Identity (Int, Bool)
testChain = KCCons (,)   id    (\case {}) (Keyed #hello (Identity 10))
          . KCCons const (,()) (\case {}) (Keyed #world (Identity True))
          $ KCNil  ()

data Intersections :: [Symbol] -> Type -> Type -> Type where
    INil  :: a -> Intersections '[] n a
    ICons :: (a -> b -> c)
          -> (c -> (a, b))
          -> NP (Not :.: Elem js) ks
          -> TSType ('Just ks) n a
          -> Intersections js n b
          -> Intersections (ks ++ js) n c

instance Invariant (Intersections ks f) where
    invmap f g = \case
      INil x -> INil (f x)
      ICons h j ns x xs -> ICons (\r -> f . h r) (j . g) ns x xs

runCoIntersections
    :: forall kss n f. Applicative f
    => (forall ks. TSType ('Just ks) n ~> f)
    -> Intersections kss n ~> f
runCoIntersections f = go
  where
    go :: Intersections jss n ~> f
    go = \case
      INil x -> pure x
      ICons g _ _ t ts -> liftA2 g (f t) (go ts)

runContraIntersections
    :: forall kss n f. Divisible f
    => (forall ks. TSType ('Just ks) n ~> f)
    -> Intersections kss n ~> f
runContraIntersections f = go
  where
    go :: Intersections jss n ~> f
    go = \case
      INil _           -> conquer
      ICons _ g _ t ts -> divide g (f t) (go ts)

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
    :: forall a b c n ks js. ()
    => (a -> b -> c)
    -> (c -> (a, b))
    -> NP (Not :.: Elem js) ks
    -> Intersections ks n a
    -> Intersections js n b
    -> Intersections (ks ++ js) n c
appendIntersections f g ns = \case
    INil x -> invmap (f x) (snd . g)
    ICons h k ms (x :: TSType ('Just as) n q) (xs :: Intersections bs n r) -> case takeNP @as @bs ms ns of
      (here, there) ->
        case assocConcat @as @bs @js here of
          Refl -> ICons               (\a (b, c) -> f (h a b) c) (B.assoc . first k . g) (concatNotElem' there here) x
                . appendIntersections (,) id there xs

injectIntersection :: TSType ('Just as) n a -> Intersections as n a
injectIntersection x = case appendNil ks of
    Refl -> ICons const (,()) (hmap (\_ -> Comp (Not (\case {}))) ks) x (INil ())
  where
    ks = typeStructure x

keyChainKeys
    :: KeyChain ks f a
    -> NP Key ks
keyChainKeys = \case
    KCNil _ -> Nil
    KCCons _ _ _ (Keyed k _) xs -> k :* keyChainKeys xs

intersectionsKeys
    :: Intersections ks n a
    -> NP Key ks
intersectionsKeys = \case
    INil _ -> Nil
    ICons _ _ _ x xs -> typeStructure x `appendNP` intersectionsKeys xs

typeStructure :: TSType ('Just as) n a -> NP Key as
typeStructure = \case
    TSObject ts -> keyChainKeys ts
    TSIntersection ts -> intersectionsKeys ts
    TSNamed _ t -> typeStructure t

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

data TSType :: Maybe [Symbol] -> Type -> Type -> Type where
    TSArray        :: ListOf (TSType ks n) a -> TSType 'Nothing n a
    TSTuple        :: PreT Ap (TSType_ n) a -> TSType 'Nothing n a
    TSObject       :: KeyChain ks (TSType_ n) a -> TSType ('Just ks) n a
    TSUnion        :: PostT Dec (TSType_ n) a -> TSType 'Nothing n a
    TSNamed        :: n -> TSType ks n a -> TSType ks n a
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
    TSIntersection :: Intersections ks n a -> TSType ('Just ks) n a
    TSPrimType     :: PS TSPrim a -> TSType 'Nothing n a

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

data Mapping k v = k :-> v

data MapElem :: [Mapping k v] -> k -> v -> Type where
    MEZ :: MapElem ((k ':-> v) ': kvs) k v
    MES :: !(MapElem kvs k v) -> MapElem (kv ': kvs) k v

data MapChange :: [Mapping k v] -> [Mapping k v] -> k -> v -> v -> Type where
    MCZ :: MapChange ((k ':-> v) ': kvs) ((k ':-> u) ': kvs) k v u
    MCS :: !(MapChange kvs kus k v u) -> MapChange (kv ': kvs) (ku ': kus) k v u

ppType
    :: TSType ks Void a
    -> PP.Doc x
ppType = \case
    TSArray t   -> getConst (interpretListOf (Const . ppType) t) PP.<+> "[]"
    TSTuple ts  -> PP.encloseSep "[" "]" ", " (icollect (withTSType_ ppType) ts)
    TSObject ts -> PP.encloseSep "{" "}" "," . getConst $
      runCoKeyChain (\k x -> Const [PP.pretty k PP.<+> ": " PP.<+> withTSType_ ppType x]) ts
    TSUnion ts  -> PP.encloseSep "" "" " | " (icollect (withTSType_ ppType) ts)
    TSNamed v _ -> absurd v
    TSIntersection ts  -> PP.encloseSep "" "" " & " . getConst $
      runCoIntersections (\x -> Const [ppType x]) ts
    TSPrimType PS{..} -> ppPrim psItem

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

objTypeToValue :: TSType ('Just ks) n a -> a -> [A.Pair]
objTypeToValue = \case
    TSObject       ts -> getOp (runContraKeyChain (\k t -> Op $ \x -> [k A..= withTSType_ typeToValue t x]) ts)
    TSIntersection ts -> getOp (runContraIntersections (Op . objTypeToValue) ts)
    TSNamed      _ t  -> objTypeToValue t

nonObjTypeToValue
    :: TSType 'Nothing n a -> a -> A.Value
nonObjTypeToValue = \case
    TSArray ts  -> A.Array
                 . V.fromList
                 . getOp (interpretListOf (\t -> Op (map (typeToValue t))) ts)
    TSTuple ts  -> A.Array
                 . V.fromList
                 . getOp (preDivisibleT (\t -> Op $ \x -> [withTSType_ typeToValue t x]) ts)
    TSUnion ts  -> iapply (withTSType_ typeToValue) ts
    TSNamed _ t -> typeToValue t
    TSPrimType PS{..} -> primToValue psItem . psSerializer

typeToValue
    :: TSType ks n a -> a -> A.Value
typeToValue = \case
    TSArray ts  -> A.Array
                 . V.fromList
                 . getOp (interpretListOf (\t -> Op (map (typeToValue t))) ts)
    TSTuple ts  -> A.Array
                 . V.fromList
                 . getOp (preDivisibleT (\t -> Op $ \x -> [withTSType_ typeToValue t x]) ts)
    TSObject ts -> A.object
                 . getOp (runContraKeyChain (\k t -> Op $ \x -> [k A..= withTSType_ typeToValue t x]) ts)
    TSUnion ts  -> iapply (withTSType_ typeToValue) ts
    TSNamed _ t -> typeToValue t
    TSIntersection ts -> A.object
                       . getOp (runContraIntersections (Op . objTypeToValue) ts)
    TSPrimType PS{..} -> primToValue psItem . psSerializer

data ParseErr = PEInvalidEnum [(Text, EnumLit)]
              | PEInvalidString Text Text
              | PEInvalidNumber Scientific Scientific
              | PEInvalidBigInt Integer Integer
              | PEPrimitive Text
              | PENever

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

parseType
    :: TSType ks n a
    -> ABE.Parse ParseErr a
parseType = \case
    TSArray ts -> unwrapFunctor $ interpretListOf (WrapFunctor . ABE.eachInArray . parseType) ts
    TSTuple ts -> flip evalStateT 0 $ (`interpret` ts) $ \t -> StateT $ \i ->
      (,i+1) <$> ABE.nth i (withTSType_ parseType t)
    TSObject ts -> (`runCoKeyChain` ts) $ \k t -> ABE.key k (withTSType_ parseType t)
    TSUnion ts -> foldr @[] (ABE.<|>) (ABE.throwCustomError PENever) $
        icollect (interpretPost (withTSType_ parseType)) (unPostT ts)
    TSNamed _ t -> parseType t
    TSIntersection ts -> runCoIntersections parseType ts
    TSPrimType PS{..} -> either (ABE.throwCustomError . PEPrimitive) pure . psParser
                     =<< parsePrim psItem

npToList :: (forall x. f x -> b) -> NP f as -> [b]
npToList f = \case
    Nil -> []
    x :* xs -> f x : npToList f xs

npToList2 :: (forall x. f x -> g x -> b) -> NP f as -> NP g as -> [b]
npToList2 f = \case
    Nil -> \case
      Nil -> []
    x :* xs -> \case
      y :* ys -> f x y : npToList2 f xs ys

zipPS :: (forall x. f x -> g x -> b) -> NP f as -> NS g as -> b
zipPS f = \case
    Nil -> \case {}
    x :* xs -> \case
      Z y  -> f x y
      S ys -> zipPS f xs ys

appendNP :: NP f as -> NP f bs -> NP f (as ++ bs)
appendNP = \case
    Nil -> id
    x :* xs -> (x :*) . appendNP xs

traverseNP
    :: Applicative h
    => (forall x. f x -> h (g x))
    -> NP f as
    -> h (NP g as)
traverseNP f = \case
    Nil -> pure Nil
    x :* xs -> (:*) <$> f x <*> traverseNP f xs

imapNP
    :: (forall x. (h x -> NS h as) -> f x -> g x)
    -> NP f as
    -> NP g as
imapNP f = \case
    Nil -> Nil
    x :* xs -> f Z x :* imapNP (f . (S .)) xs
