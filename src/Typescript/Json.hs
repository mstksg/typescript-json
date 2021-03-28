{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

module Typescript.Json (
  -- * TSType
    TSType
  , TSTypeF
  , EnumLit(..)
  , TSType_(..)
  , TSTypeF_(..)
  -- * Construction
  -- ** Lists and Nullables
  , tsList, tsVector, tsIsList
  -- ** Object
  , ObjectProps(..)
  , keyVal, keyValMay, tsObject
  -- ** Tuple
  , TupleVals(..)
  , tupleVal, tsTuple
  , stripObjectVals
  -- ** Unions
  , tsUnion, tsUnions
  -- *** Tagged
  , tagVal, taggedObject, taggedValue, taggedNullary
  , TaggedBranches(..)
  , Branch(..)
  , TaggedValueOpts(..)
  , taggedBranch
  , mergeTB
  , emptyTaggedBranch
  , tsTaggedUnion
  , tsTaggedUnions
  -- ** Intersections
  , IntersectVals(..)
  , intersectVal, tsIntersection
  -- ** Named
  , tsNamed, tsNamed_
  -- ** Generics
  , tsGeneric
  , tsGeneric1
  , tsGeneric2
  , tsGeneric3
  , tsGenericInterface
  , tsApplied1
  , tsApplied2
  , tsApplied3
  , tsApplied
  , tsApply1
  , tsApply2
  , tsApply3
  , tsApply
  -- ** Primitives
  , tsBoolean
  , tsNumber, tsBoundedInteger, tsInteger, tsRealFloat, tsDouble, tsBigInt
  , tsText, tsLazyText, tsString
  , tsStringLit, tsNumericLit, tsIntegerLit, tsBigIntLit
  , tsUnknown, tsAny, tsVoid, tsUndefined, tsNull, tsNever
  , tsMaybe
  -- ** Builidng Enum
  -- *** With Vector
  , FinIso(..), tsEnumWith, tsIntEnumFrom, tsIntEnum
  -- *** With Map
  , EnumMap(..), tsEnumMap
  -- *** With Enum
  , tsFinEnum, tsFinIntEnum
  -- * Printing
  , ppType
  , ppNamed
  , typeExports'
  , typeExports
  , typeExports_
  , namedTypeExports'
  , namedTypeExports
  , namedTypeExports_
  -- * Serializing
  , encodeType
  , encodeTypeStrict
  , typeToValue
  -- * Parsing
  , decodeType
  , decodeTypeStrict
  , parseType
  ) where

import           Control.Applicative.Free
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Default.Class
import           Data.Fin hiding                   (absurd)
import           Data.Foldable
import           Data.Functor.Apply
import           Data.Functor.Combinator
import           Data.Functor.Contravariant
import           Data.Functor.Invariant
import           Data.Functor.Invariant.DecAlt
import           Data.HFunctor.Route
import           Data.Map                          (Map)
import           Data.Profunctor
import           Data.SOP                          (NP(..), NS(..), I(..))
import           Data.Scientific
import           Data.Text                         (Text)
import           Data.Traversable
import           Data.Type.Nat                     (Plus)
import           Data.Vec.Lazy                     (Vec)
import           Data.Void
import           Typescript.Json.Core.Encode
import           Typescript.Json.Core.Parse
import           Typescript.Json.Core.Print
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators
import qualified Control.Applicative.Lift          as Lift
import qualified Data.Aeson                        as A
import qualified Data.Aeson.BetterErrors           as ABE
import qualified Data.Aeson.Encoding               as AE
import qualified Data.ByteString                   as BS
import qualified Data.ByteString.Lazy              as BSL
import qualified Data.Fin.Enum                     as FE
import qualified Data.Map                          as M
import qualified Data.Set                          as S
import qualified Data.Text                         as T
import qualified Data.Text.Lazy                    as TL
import qualified Data.Type.Nat                     as Nat
import qualified Data.Vec.Lazy                     as Vec
import qualified Data.Vector.Generic               as V
import qualified GHC.Exts                          as Exts

-- | A type aggregating key-value pairs for an object.  Meant to
-- be assembled using 'keyVal' (for required properties) and 'keyValMay'
-- (for optional properties) and combined using its 'Applicative' instance.
-- To finally turn one into a 'TSType', use 'tsObject'.
--
-- In a @'ObjectProps' p a b@, the @a@ represents the overall aggregate
-- type, and the @b@ represents the type of the part that this 'ObjectProps'
-- is describing.
--
-- @
-- data MyType = MyType
--   { mta :: Int
--   , mtb :: Bool
--   , mtc :: Maybe String
--   }
--
-- myTypeProps :: 'ObjectProps' p MyType MyType
-- myTypeProps = MyType
--   <$> 'keyVal' True mta "mta" ('TSType_' 'tsBoundedInteger')
--   <*> keyVal True mtb "mtb" (TSType_ 'tsBoolean')
--   <*> 'keyValMay' mtc "mtc" (TSType_ 'tsString')
--
-- myType :: TSType p 'IsObj MyType
-- myType = tsObject myTypeProps
-- @
--
-- @
-- ppType myType
-- -- => { mta: number, mtb: boolean, mtc?: string }
-- @
--
-- In the above, @keyVal True mta "mta" tsBoundedInteger@ has the type
-- @ObjectProps p MyType Int@, showing that it refers to the @Int@ field
-- of the @MyType@.  The trick to using this is to assemble 'ObjectProps'
-- together using Applicative combinators until the @a@ and @b@ "match",
-- and the 'ObjectProps' describes the entire value.  Then you can use
-- 'tsObject'.
newtype ObjectProps p a b = ObjectProps
    { getObjectProps :: Ap (Pre a (ObjMember (TSType_ p))) b }
  deriving newtype (Functor, Apply, Applicative)

instance Invariant (ObjectProps p a) where
    invmap f _ = fmap f

instance Profunctor (ObjectProps p) where
    dimap f g = ObjectProps . hmap (mapPre f) . fmap g . getObjectProps

-- | Create a single key-value pair for an object.  If the first argument
-- is 'True', will try to turn any nullable value into an optional property
-- with non-nullable type if possible.  Otherwise, always uses a required
-- property.
keyVal
    :: Bool             -- ^ turn nullable types into optional params if possible
    -> (a -> b)         -- ^ project this pair's value out of the aggregate type
    -> Text             -- ^ key (property name)
    -> TSType_ p b
    -> ObjectProps p a b
keyVal True f k (TSType_ t) = ObjectProps . injectPre f $ ObjMember
    { objMemberKey = k
    , objMemberVal = case isNullable t of
        Nothing -> L1 $ TSType_ t
        Just u  -> R1 $ hmap TSType_ u
    }
keyVal False f k t = ObjectProps . injectPre f $ ObjMember
    { objMemberKey = k
    , objMemberVal = L1 t
    }

-- | Create a single optional key-value pair for an object.
keyValMay
    :: (a -> Maybe b)   -- ^ project this pair's value out of the aggregate type, potentially revealing it is not present.
    -> Text             -- ^ key (property name)
    -> TSType_ p b
    -> ObjectProps p a (Maybe b)
keyValMay f k t = ObjectProps . injectPre f $ ObjMember
    { objMemberKey = k
    , objMemberVal = R1 (ilan t)
    }

-- | Gather together object properties into a 'TSType'.  See 'ObjectProps'
-- for details on how to use this.
tsObject
    :: ObjectProps p a a
    -> TSType p 'IsObj a
tsObject = TSObject . PreT . getObjectProps

-- | A type aggregating values in a tuple type.  Meant to
-- be assembled using 'tupleVal' and combined using its 'Applicative'
-- instance.  To finally turn one into a 'TSType', use 'tsTuple'.
--
-- In a @'TupleVals' p a b@, the @a@ represents the overall aggregate
-- type, and the @b@ represents the type of the part that this 'TupleVals'
-- is describing.
--
-- @
-- data MyType = MyType
--   { mta :: Int
--   , mtb :: Bool
--   , mtc :: String
--   }
--
-- myTypeVals :: 'TupleVals' p MyType MyType
-- myTypeVals = MyType
--   <$> 'tupleVal' mta (TSType_ 'tsBoundedInteger')
--   <*> tupleVal mtb (TSType_ 'tsBoolean')
--   <*> tupleVal mtc (TSType_ 'tsString')
--
-- myType :: TSType p 'NotObj MyType
-- myType = tsTuple myTypeVals
-- @
--
-- @
-- ppType myType
-- -- => [number, boolean, string]
-- @
--
-- In the above, @tupleVal mta tsBoundedInteger@ has the type
-- @TupleVals p MyType Int@, showing that it refers to the @Int@ field
-- of the @MyType@.  The trick to using this is to assemble 'TupleVals'
-- together using Applicative combinators until the @a@ and @b@ "match",
-- and the 'TupleVals' describes the entire value.  Then you can use
-- 'tsTuple'.
--
-- Note that the order that the 'Applicative' combination matters: it
-- determines the ordering of the tuple.
newtype TupleVals p a b = TupleVals
    { getTupleVals :: Ap (Pre a (TSType_ p)) b }
  deriving newtype (Functor, Apply, Applicative)

instance Invariant (TupleVals p a) where
    invmap f _ = fmap f

instance Profunctor (TupleVals p) where
    dimap f g = TupleVals . hmap (mapPre f) . fmap g . getTupleVals

-- | Create a singleton 'TupleVals', to be combined with applicative
-- combinators with others.
tupleVal
    :: (a -> b)         -- ^ project this pair's value out of the aggregate type
    -> TSType_ p b
    -> TupleVals p a b
tupleVal f = TupleVals . injectPre f

-- | Gather together tuple values into a 'TSType'.  See 'TupleVals' for
-- details on how to use this.
tsTuple
    :: TupleVals p a a
    -> TSType p 'NotObj a
tsTuple = TSTuple . PreT . getTupleVals

stripObjectVals :: ObjectProps p a b -> TupleVals p a b
stripObjectVals = TupleVals
                . hmap (hmap ((id !*! go) . objMemberVal))
                . getObjectProps
  where
    go (ILan f g (TSType_ x)) = TSType_ . invmap f g $ mkNullable x


-- | A type aggregating branches in a union type.  Meant to
-- be assembled using 'unionBranch' and combined using its 'Decide'
-- instance.  To finally turn one into a 'TSType', use 'tsUnion'.
--
-- In a @'UnionBranches' p a b@, the @a@ represents the overall aggregate
-- type, and the @b@ represents the type of the part that this
-- 'UnionBranches'
-- is describing.
--
-- @
-- data MyType = MTA Int | MTB Bool
--
-- myTypeBranches :: UnionBranches p MyType MyType
-- myTypeBranches = 'decide' (\case MTA i -> Left i; MTB b -> Right b)
--     ('unionBranch' MTA (TSType_ 'tsBoundedInteger'))
--     ('unionBranch' MTB (TSType_ 'tsBoolean'))
--
-- myType :: TSType p 'NotObj MyType
-- myType = tsUnion myTypeBranches
-- @
--
-- @
-- ppType myType
-- -- => number | boolean
-- @
--
-- In the above, @tupleVal mta tsBoundedInteger@ has the type
-- @UnionBranches p MyType Int@, showing that it refers to the @Int@ field
-- of the @MyType@.  The trick to using this is to assemble 'UnionBranches'
-- together using Decide combinators until the @a@ and @b@ "match",
-- and the 'UnionBranches' describes the entire value.  Then you can use
-- 'tsUnion'.
--
-- Note that 'Decide' combinators can be a bit tedious to use if you have
-- a large number of branches.  'tsUnions' is an alternative to decide
-- combinators that uses heterogeneous lists, which can potentially make
-- things cleaner.

-- | Build up a union type from a 'unionBranch'.
tsUnion
    :: TSUnionBranches p a
    -> TSType p 'NotObj a
tsUnion = TSUnion

-- | A convenient way to combine multiple unions using 'NP' and 'NS'.
-- Takes a function to "break" the final type into each branch ('NS') and a tuple
-- ('NP') to handle each branch.
--
-- @
-- data MyType = MTA Int | MTB Bool | MTC String | MTD Double
--
-- subtypes :: NP (Dec (Post MyType (TSType_ p)) '[Int, Bool, String, Double]
-- subtypes = 'unionBranch' MTA (TSType_ 'tsBoundedInteger')
--         ':*' unionBranch MTB (TSType_ 'tsBoolean')
--         :* unionBranch MTC (TSType_ 'tsString')
--         :* unionBranch MTD (TSType_ 'tsDouble')
--         :* 'Nil'
--
-- myType :: TSType p 'NotObj MyType
-- myType = tsUnions splitMyType subtypes
--   where
--     splitMyType = \case
--       MTA i -> Z (I i)
--       MTB b -> S (Z (I b))
--       MTC s -> S (S (S (I s)))
--       MTA d -> S (S (S (S (I d))))
-- @
--
-- This is essentially a wrapper over repeated 'decide's and 'tsUnion', but
-- can be cleaner than peeling of 'Either's.
tsBranchUnions
    :: (a -> NS I (b ': bs))
    -> NP (Op a) (b ': bs)
    -> NP (TSUnionBranches p) (b ': bs)
    -> TSType p 'NotObj a
tsBranchUnions f g = tsUnion
                   . invmap (unHandlers g) f
                   . concatDecAlt1

tsUnions
    :: (a -> NS I (b ': bs))
    -> NP (Op a) (b ': bs)
    -> NP (TSType_ p) (b ': bs)
    -> TSType p 'NotObj a
tsUnions f g = tsUnion
             . invmap (unHandlers g) f
             . concatDecAlt1
             . hmap inject

unHandlers :: NP (Op a) as -> NS I as -> a
unHandlers = \case
    Nil -> \case {}
    Op f :* xs -> \case
      Z (I x) -> f x
      S hs -> unHandlers xs hs

data Branch p a = Branch
    { branchTag   :: Text
    , branchType  :: Lift (TSType_ p) a
    }

instance Invariant (Branch p) where
    invmap f g (Branch a b) = Branch a (invmap f g b)

-- | A high-level data type describing the common pattern of a "tagged"
-- union (sum types in Haskell), where each branch comes in the form of an
-- object with a "tag" property with a string literal singleton, and the
-- rest of the object is the contents.  We would store an @Either Int Bool@ as, say,
-- @{ tag: "Left", contents: number } | { tag: "Right", contents: boolean }@.
--
-- Meant to be constructed using 'taggedBranch' and other 'Decide'
-- combinators.
newtype TaggedBranches p a = TaggedBranches
    { getTaggedBranches :: DecAlt1 (Branch p) a }
  deriving newtype (Invariant)

mergeTB
    :: (a -> Either b c)
    -> (b -> a)
    -> (c -> a)
    -> TaggedBranches p b
    -> TaggedBranches p c
    -> TaggedBranches p a
mergeTB f ga gb (TaggedBranches x) (TaggedBranches y) = TaggedBranches $
    swerve1 f ga gb x y

-- | Create a singleton 'TaggedBranches', to be combined with 'Decide'
-- combinators with others.  Can also be used with 'tsUnions' if you want
-- to combine a large number.
taggedBranch
    :: Text             -- ^ Tag value
    -> TSType_ p a
    -> TaggedBranches p a
taggedBranch v = TaggedBranches . inject . Branch v . Lift.Other

emptyTaggedBranch
    :: Text             -- ^ Tag value
    -> a                -- ^ Pure "singleton"/literal rep value (ignored, just use ())
    -> TaggedBranches p a
emptyTaggedBranch v = TaggedBranches . inject . Branch v . Lift.Pure

tsTaggedUnion
    :: TaggedValueOpts
    -> TaggedBranches p a
    -> TSType p 'NotObj a
tsTaggedUnion tvo = tsUnion . runTaggedBranches tvo

tsTaggedUnions
    :: TaggedValueOpts
    -> (a -> NS I (b ': bs))
    -> NP (Op a) (b ': bs)
    -> NP (TaggedBranches p) (b ': bs)
    -> TSType p 'NotObj a
tsTaggedUnions tvo f g = tsBranchUnions f g . hmap (runTaggedBranches tvo)

runTaggedBranches
    :: TaggedValueOpts
    -> TaggedBranches p a
    -> TSUnionBranches p a
runTaggedBranches tvo = hmap (runBranch tvo) . getTaggedBranches

runBranch
    :: TaggedValueOpts
    -> Branch p a
    -> TSType_ p a
runBranch tvo Branch{..} = case branchType of
    Lift.Pure  x -> taggedNullary tvo branchTag x
    Lift.Other t -> TSType_ $ taggedValue tvo branchTag t

data TaggedValueOpts =
    TVOTagAndContents TagAndContents
  | TVOTagIsKey TagIsKey
  deriving (Show, Eq, Ord)

data TagAndContents = TagAndContents
    { tacMergeTagValue :: Bool  -- ^ if possible, flatten the object under contents
    , tacTagKey        :: Text
    , tacContentsKey   :: Text
    }
  deriving (Show, Eq, Ord)

data TagIsKey = TagIsKey
    { tikNullaryIsString :: Bool  -- ^ nullary constructors are just string literals. if False, they are { tag: null }.
    }
  deriving (Show, Eq, Ord)

instance Default TagAndContents where
    def = TagAndContents
        { tacMergeTagValue = False
        , tacTagKey = "tag"
        , tacContentsKey = "contents"
        }

instance Default TagIsKey where
    def = TagIsKey { tikNullaryIsString = True }

instance Default TaggedValueOpts where
    def = TVOTagAndContents def

-- | A utility for a simple situation of a "tag" key-value pair, where the
-- property value is just a string literal singleton.  Often used to
-- simulate discriminated unions in typescript.
--
-- @
-- ppType . TSType_ . tsObject $
--   tagVal "tag" "something"
-- -- => { tag: "sometning" }
-- @
--
-- You can combine this with other properties:
--
-- @
-- 'ppType' . 'TSType_' . 'tsObject' $
--      'tagVal' "tag" "something"
--   *> 'keyVal' True "contents" id 'tsBoolean'
-- -- => { tag: "someting", contents: boolean }
-- @
--
-- See also 'taggedObject', which uses an intersection instead of joining
-- the keys directly.
tagVal
    :: Text         -- ^ tag key
    -> Text         -- ^ tag value
    -> ObjectProps p a ()
tagVal tag val = keyVal False (const ()) tag $ TSType_ (tsStringLit val)

-- | A utility for a simple situation of a "tag" key-value pair intersected
-- with an object type.  Often used to simulate discriminated unions in
-- typescript.
--
-- @
-- 'ppType' . 'TSType_' $
--      'taggedObject' "tag" "something" $
--          'tsObject' $
--            (,) <$> 'keyVal' True "name" fst (TSType_ 'tsText')
--                <*> 'keyVal' True "age" snd (TSType_ 'tsBoundedInteger')
-- -- => { tag: "something" } & { name: string, age: number }
-- @
--
-- See also 'taggedObject', which uses an intersection instead of joining
-- the keys directly.
taggedObject
    :: Text                   -- ^ tag key
    -> Text                   -- ^ tag value
    -> TSType p 'IsObj a    -- ^ contents (object)
    -> TSType p 'IsObj a
taggedObject tag val obj = tsIntersection $
       intersectVal (const ()) (tsObject (tagVal tag val))
    .> intersectVal id         obj

-- | High-level utility to wrap a 'TSType_' with a "tag".
--
-- Assuming both flags are set to 'True':
--
-- 1. If the contents type is an object, this will be @{ tagkey: tagvalue } & contents@ (the same behavior as 'taggedObject').
-- 2. If the contents type is a nullable value, this well be @{ tagkey: tagvalue, contentskey?: contents}@
-- 3. Otherwise, this well be @{ tagkey: tagvalue, contentskey: contents}@
--
-- If the first argument is 'False', will avoid case (1).  If the second argument
-- is 'False', will avoid case (2).
--
-- @
-- case1 :: TSType_ p (Text, Int)
-- case1 = 'TSType_' . 'tsObject' $
--   (,) <$> 'keyVal' True "name" fst (TSType_ 'tsText')
--       <*> 'keyVal' True "age" snd (TSType_ 'tsBoundedInteger')
--
-- case2 :: TSType_ p (Maybe Int)
-- case2 = 'TSType_' $ 'tsNullable' ('TSType_' 'tsBoundedInteger')
--
-- case3 :: TSType_ p String
-- case3 = 'TSType_' 'tsString'
-- @
--
-- @
-- 'ppType' . 'TSType_' $ 'taggedValue' True True "tag" "something" "contents" case1
-- -- => { tag: "something" } & { name: string, age: number }
--
-- 'ppType' . 'TSType_' $ 'taggedValue' True True "tag" "something" "contents" case2
-- -- => { tag: "something", contents?: number }
--
-- 'ppType' . 'TSType_' $ 'taggedValue' True True "tag" "something" "contents" case3
-- -- => { tag: "something", contents: string }
-- @
taggedValue
    :: TaggedValueOpts
    -> Text            -- ^ tag value
    -> TSType_ p a     -- ^ contents type
    -> TSType p 'IsObj a
taggedValue tvo tagValue t = case tvo of
    TVOTagAndContents TagAndContents{..}
      | tacMergeTagValue -> case decideTSType_ t of
          L1 x -> tsObject $ tagVal tacTagKey tagValue
                          *> keyVal False id tacContentsKey (TSType_ x)
          R1 y
            -- TODO: if the tag key is a key in the obj, then dont do it
            | tacTagKey `S.member` isObjKeys y
                -> tsObject $ tagVal tacTagKey tagValue
                           *> keyVal False id tacContentsKey t
            | otherwise -> taggedObject tacTagKey tagValue y
      | otherwise -> tsObject $
             tagVal tacTagKey tagValue
          *> keyVal False id tacContentsKey t
    TVOTagIsKey TagIsKey{..} -> tsObject $ keyVal False id tagValue t

taggedNullary
    :: TaggedValueOpts
    -> Text
    -> a
    -> TSType_ p a
taggedNullary tvo tagValue x = invmap (const x) (const ()) $ case tvo of
    TVOTagAndContents TagAndContents{..} ->
        TSType_ $ tsObject (tagVal tacTagKey tagValue)
    TVOTagIsKey TagIsKey{..}
      | tikNullaryIsString -> TSType_ $ tsStringLit tagValue
      | otherwise          -> TSType_ $ tsObject (keyVal False id tagValue (TSType_ tsNull))

-- | A type aggregating the parts of an intersection.  Meant to be
-- assembled using 'intersectVal' and combined using its 'Applicative'
-- instance.  To finally turn one into a 'TSType', use 'tsIntersection'.
--
-- In a @'IntersectVals' p a b@, the @a@ represents the overall aggregate
-- type, and the @b@ represents the type of the part that this 'IntersectVals'
-- is describing.
--
-- @
-- data MyType = MyType
--   { mta :: Int
--   , mtb :: Bool
--   , mtc :: Maybe String
--   }
--
-- myType :: TSType p 'IsObj MyType
-- myType = tsObject $ MyType
--   <$> 'keyVal' True mta "mta" ('TSType_' 'tsBoundedInteger')
--   <*> keyVal True mtb "mtb" (TSType_ 'tsBoolean')
--   <*> 'keyValMay' mtc "mtc" (TSType_ 'tsString')
--
-- -- { tag: "something" }
-- tagType :: TSType p 'IsObj ()
-- tagType = tagVal "tag" "something"
--
-- myTaggedType :: IntersectVals p MyType MyType
-- myTaggedType = intersectVal tagType
--             .> intersectVal myType
-- @
--
-- @
-- ppType $ tsIntersection myTaggedType
-- -- => { tag: "something" } &  { mta: number, mtb: boolean, mtc?: string }
-- @
--
-- This works in the same style as 'TupleVals' and 'ObjectProps', so see
-- those types for more examples of using an 'Applicative' instance.
--
-- If any of the objects in the intersection have duplicate keys of the
-- same type, the property value from the rightmost branch will be used
-- when decoding.
--
-- If any of the objects in the intersection have duplicate keys of
-- different types, this describes an invalid typescript type.  The
-- behavior of encoding/decoding is undefined; for encoding, the result
-- will most likely not typecheck in typescript.  for decoding, the result
-- will most likely fail to parse.
newtype IntersectVals p a b = IntersectVals
    { getIntersectVals :: Ap1 (Pre a (TSType p 'IsObj)) b }
  deriving newtype (Functor, Apply)

instance Invariant (IntersectVals p a) where
    invmap f _ = fmap f

instance Profunctor (IntersectVals p) where
    dimap f g = IntersectVals . hmap (mapPre f) . fmap g . getIntersectVals

-- | Create a singleton 'IntersectVals', to be combined with applicative
-- combinators with others.
--
-- Note that the input type must an object literal, indicated by @''IsObj'@
intersectVal
    :: (a -> b)
    -> TSType p 'IsObj b
    -> IntersectVals p a b
intersectVal f = IntersectVals . injectPre f

-- | Gather together intersection values into a 'TSType'.  See
-- 'IntersectionVals' for details on how to use this.
tsIntersection
    :: IntersectVals p a a
    -> TSType p 'IsObj a
tsIntersection = TSIntersection . PreT . getIntersectVals

data EnumMap a = EnumMap
    { emGet :: Map EnumLit (Text, a)
    , emPut :: a -> EnumLit
    }
-- the main issue is neeing to not require a to be Eq or anything and so
-- not requiring a lookup. the partial part is making sure every enumlit is
-- in the map

runEnumMap :: EnumMap a -> (forall n. FinIso n a -> Vec n (Text, EnumLit) -> r) -> r
runEnumMap EnumMap{..} f = Vec.reifyList (M.toList emGet) $ \(xs :: Vec n (EnumLit, (Text, a))) ->
    let res :: Vec n (Text, EnumLit)
        res = fmap (\(l,(c,_)) -> (c, l)) xs
        outVec = snd . snd <$> xs
        xsMap :: Map EnumLit (Fin n)
        xsMap = M.fromList . toList $ Vec.imap (\i (l, _) -> (l, i)) xs
        lu k = case M.lookup (emPut k) xsMap of
          Nothing -> error $ "Bad EnumMap given when using tsEnumMap: Map missing key " <> show (emPut k)
          Just x  -> x
        fi = FinIso
          { fiGet = (outVec Vec.!)
          , fiPut = lu
          }
    in  f fi res

tsEnumMap :: Text -> EnumMap a -> TSNamed p 'NotObj '[] '[] a
tsEnumMap nm em = runEnumMap em (tsEnumWith nm)

tsFinEnum
    :: FE.Enum a
    => Text
    -> Vec (FE.EnumSize a) (Text, EnumLit)
    -> TSNamed p 'NotObj '[] '[] a
tsFinEnum nm = tsEnumWith nm $ FinIso
    { fiGet = FE.to
    , fiPut = FE.from
    }

tsFinIntEnum
    :: FE.Enum a
    => Text
    -> Vec (FE.EnumSize a) Text
    -> TSNamed p 'NotObj '[] '[] a
tsFinIntEnum nm = tsIntEnum nm $ FinIso
    { fiGet = FE.to
    , fiPut = FE.from
    }


data FinIso n a = FinIso
    { fiGet :: Fin n -> a
    , fiPut :: a -> Fin n
    }

instance Invariant (FinIso n) where
    invmap f g (FinIso x y) = FinIso (f . x) (y . g)

tsEnumWith
    :: Text
    -> FinIso n a
    -> Vec n (Text, EnumLit)
    -> TSNamed p 'NotObj '[] '[] a
tsEnumWith nm FinIso{..} xs = TSNamed
    { tsnName = nm
    , tsnType = TSNPrimType $
        invmap fiGet fiPut $ inject (TSEnum xs)
    }

tsIntEnum
    :: Text
    -> FinIso n a
    -> Vec n Text
    -> TSNamed p 'NotObj '[] '[] a
tsIntEnum nm = tsIntEnumFrom nm 0

tsIntEnumFrom
    :: Text
    -> Int
    -> FinIso n a
    -> Vec n Text
    -> TSNamed p 'NotObj '[] '[] a
tsIntEnumFrom nm i0 fi xs = tsEnumWith nm fi xs'
  where
    xs' = flip evalState i0 . for xs $ \x -> state $ \i ->
      ((x, ELNumber (fromIntegral i)), i+1)


-- | Wrap a type in a name, in a way that preserves @k@ (whether or not the
-- type is an object literal).
tsNamed
    :: Text
    -> TSType p k a
    -> TSNamed p k '[] '[] a
tsNamed nm t = TSNamed
    { tsnName = nm
    , tsnType = TSNFunc (TSGeneric Nil2 (\n _ -> tsShift n t))
    }
-- TODO: namespacing

-- | Wrap a type in a name.
--
-- When printing this type, only the name will appear.  However, when
-- generating exports ('typeExports', 'typeExportsF'), these named types
-- will be extracted and de-duplicated to the top level.
--
-- If the same name appears twice within a type, it must describe the same
-- type underneath.  Otherwise, behavior is undefined.
tsNamed_
    :: Text
    -> TSType_ p a
    -> TSNamed_ p '[] '[] a
tsNamed_ nm = withTSType_ (TSNamed_ . tsNamed nm)

-- | Create a single-argument generic (parameterized) type.
--
-- For example, we could make a type imitating 'Maybe' in Haskell:
--
-- @
-- mkMaybe :: TSType_ p a -> TSType_ p (Maybe a)
-- mkMaybe = tsUnion $ decide (maybe (Left ()) Right) $
--     (tsTagged
-- @
tsGeneric1
    :: Text                     -- ^ Name of the type
    -> Param p a e              -- ^ Name of the parameter (used for printing) and what it extends
    -> (forall r. SNat_ r -> Arg_ (Plus r p) a e -> TSType (Plus r p) k b)         -- ^ Make a type, given the type parameter
    -> TSNamed p k '[a] '[e] b
tsGeneric1 n p f = tsGeneric n (p :** Nil2) $ \rs (t :** Nil2) -> f rs t

tsGeneric2
    :: Text
    -> Param p a ea
    -> Param p b eb
    -> (forall r. SNat_ r -> Arg_ (Plus r p) a ea -> Arg_ (Plus r p) b eb -> TSType (Plus r p) k c)
    -> TSNamed p k '[a, b] '[ea, eb] c
tsGeneric2 n p q f = tsGeneric n (p :** q :** Nil2) $
            \rs (t :** u :** Nil2) -> f rs t u

tsGeneric3
    :: Text
    -> Param p a ea
    -> Param p b eb
    -> Param p c ec
    -> (forall r. SNat_ r -> Arg_ (Plus r p) a ea -> Arg_ (Plus r p) b eb -> Arg_ (Plus r p) c ec -> TSType (Plus r p) k d)
    -> TSNamed p k '[a, b, c] '[ea, eb, ec] d
tsGeneric3 n p q r f = tsGeneric n (p :** q :** r :** Nil2) $
            \rs (t :** u :** v :** Nil2) -> f rs t u v

-- | A parameterized type with multiple parameters.
tsGeneric
    :: Text                 -- ^ Name
    -> NP2 (Param p) as es       -- ^ Name of parameters and extends
    -> (forall r. SNat_ r -> NP2 (Arg_ (Plus r p)) as es -> TSType (Plus r p) k b)   -- ^ Type function
    -> TSNamed p k as es b
tsGeneric n ps f = TSNamed
    { tsnName = n
    , tsnType = TSNFunc $ TSGeneric ps f
    }

tsGenericInterface
    :: Text             -- ^ name
    -> NP2 (Param p) as es       -- ^ Name of parameters and extends
    -> Lift (TSAppliedF p 'IsObj as es) a   -- ^ if it extends any other object
    -> (forall r. SNat_ r -> NP2 (Arg_ (Plus r p)) as es -> TSKeyVal (Plus r p) b)  -- how to use type variables
    -> TSNamed p 'IsObj as es (a, b)
tsGenericInterface n ps e f = TSNamed
    { tsnName = n
    , tsnType = TSNFunc $ TSGenericInterface ps (,) id e f
    }

tsApplied
    :: TSNamed p k as es b
    -> NP2 (Arg_ p) as es
    -> TSType p k b
tsApplied f x = TSNamedType (f :$ x)

tsApply2
    :: TSTypeF p k '[a,b] '[ea,eb] c      -- ^ type function
    -> Arg_ p a ea         -- ^ thing to apply
    -> Arg_ p b eb         -- ^ thing to apply
    -> TSType p k c
tsApply2 f t u = tsApply f (t :** u :** Nil2)

tsApply3
    :: TSTypeF p k '[a,b,c] '[ea,eb,ec] d      -- ^ type function
    -> Arg_ p a ea         -- ^ thing to apply
    -> Arg_ p b eb         -- ^ thing to apply
    -> Arg_ p c ec         -- ^ thing to apply
    -> TSType p k d
tsApply3 f t u v = tsApply f (t :** u :** v :** Nil2)

tsApplied1
    :: TSNamed p k '[a] '[e] b
    -> Arg_ p a e
    -> TSType p k b
tsApplied1 tf tx = tsApplied tf (tx :** Nil2)

tsApplied2
    :: TSNamed p k '[a, b] '[ea, eb] c
    -> Arg_ p a ea
    -> Arg_ p b eb
    -> TSType p k c
tsApplied2 tf tx ty = tsApplied tf (tx :** ty :** Nil2)

tsApplied3
    :: TSNamed p k '[a, b, c] '[ea, eb, ec] d
    -> Arg_ p a ea
    -> Arg_ p b eb
    -> Arg_ p c ec
    -> TSType p k d
tsApplied3 tf tx ty tz = tsApplied tf (tx :** ty :** tz :** Nil2)

tsList :: TSType_ p a -> TSType p 'NotObj [a]
tsList = withTSType_ (TSArray . ilan)

tsVector :: V.Vector v a => TSType_ p a -> TSType p 'NotObj (v a)
tsVector = invmap V.fromList V.toList . tsList

tsIsList :: Exts.IsList l => TSType_ p (Exts.Item l) -> TSType p 'NotObj l
tsIsList = invmap Exts.fromList Exts.toList . tsList

tsBoolean :: TSType p 'NotObj Bool
tsBoolean = TSPrimType $ inject TSBoolean

tsNumber :: TSType p 'NotObj Scientific
tsNumber = TSPrimType $ inject TSNumber

tsBoundedInteger :: (Integral a, Bounded a) => TSType p 'NotObj a
tsBoundedInteger = TSPrimType $ PS TSNumber
    (\x -> case toBoundedInteger x of
            Nothing -> Left . T.pack $ "Not an integer: " <> show x
            Just i  -> Right i
    ) fromIntegral

tsInteger :: Integral a => TSType p 'NotObj a
tsInteger = TSPrimType $ PS TSNumber
    (\x -> first (\n -> T.pack $ "Not an integer: " <> show @Double n) (floatingOrInteger x))
    fromIntegral

tsRealFloat :: RealFloat a => TSType p 'NotObj a
tsRealFloat = invmap toRealFloat fromFloatDigits tsNumber

tsDouble :: TSType p 'NotObj Double
tsDouble = tsRealFloat

tsBigInt :: TSType p 'NotObj Integer
tsBigInt = TSPrimType $ inject TSBigInt

tsText :: TSType p 'NotObj Text
tsText = TSPrimType $ inject TSString

tsLazyText :: TSType p 'NotObj TL.Text
tsLazyText = invmap TL.fromStrict TL.toStrict tsText

tsString :: TSType p 'NotObj String
tsString = invmap T.unpack T.pack tsText

tsStringLit :: Text -> TSType p 'NotObj ()
tsStringLit = TSPrimType . inject . TSStringLit

tsNumericLit :: Scientific -> TSType p 'NotObj ()
tsNumericLit = TSPrimType . inject . TSNumericLit

tsIntegerLit :: Integral a => a -> TSType p 'NotObj ()
tsIntegerLit = TSPrimType . inject . TSNumericLit . fromIntegral

tsBigIntLit :: Integer -> TSType p 'NotObj ()
tsBigIntLit = TSPrimType . inject . TSBigIntLit

tsUnknown :: TSType p 'NotObj A.Value
tsUnknown = TSPrimType $ inject TSUnknown

tsAny :: TSType p 'NotObj A.Value
tsAny = TSPrimType $ inject TSAny

-- TODO: to/from aeson parser

tsVoid :: TSType p 'NotObj ()
tsVoid = TSBaseType $ inject TSVoid

tsUndefined :: TSType p 'NotObj ()
tsUndefined = TSBaseType $ inject TSUndefined

tsNull :: TSType p 'NotObj ()
tsNull = TSBaseType $ inject TSNull

tsNever :: TSType p 'NotObj Void
tsNever = TSBaseType $ inject TSNever

tsMaybe
    :: Text         -- ^ the "nothing" constructor
    -> Text         -- ^ the "just" field
    -> TSType_ p a
    -> TSType p 'NotObj (Maybe a)
tsMaybe n j t = tsTaggedUnions
    (TVOTagIsKey def)
    (\case Nothing -> Z (I ()); Just x -> S (Z (I x)))
    (Op (const Nothing) :* Op Just :* Nil)
    (  emptyTaggedBranch "nothing" ()
    :* taggedBranch "just" t
    :* Nil
    )

-- tsTaggedUnions
--     :: TaggedValueOpts
--     -> (a -> NS I (b ': bs))
--     -> NP (Op a) (b ': bs)
--     -> NP (TaggedBranches p) (b ': bs)
--     -> TSType p 'NotObj a
--         -- tsUnion $
--     -- swerve1 (maybe (Left ()) Right) (const Nothing) Just
--         -- (inject . TSType_ $ tsStringLit n)
--         -- (inject . TSType_ $ tsObject (keyVal False id j (TSType_ t)))

encodeType :: TSType 'Nat.Z k a -> a -> BSL.ByteString
encodeType t = AE.encodingToLazyByteString . typeToEncoding t

encodeTypeStrict :: TSType 'Nat.Z k a -> a -> BS.ByteString
encodeTypeStrict t = BSL.toStrict . encodeType t

decodeType
    :: TSType 'Nat.Z k a
    -> BSL.ByteString
    -> Either (ABE.ParseError ParseErr) a
decodeType t = ABE.parse (parseType t)

decodeTypeStrict
    :: TSType 'Nat.Z k a
    -> BS.ByteString
    -> Either (ABE.ParseError ParseErr) a
decodeTypeStrict t = ABE.parseStrict (parseType t)

