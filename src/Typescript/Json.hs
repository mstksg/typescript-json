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
  , tsList, tsVector, tsIsList, tsNullable
  -- ** Object
  , ObjectProps(..)
  , keyVal, keyValMay, tsObject
  -- ** Tuple
  , TupleVals(..)
  , tupleVal, tsTuple
  -- ** Unions
  , UnionBranches(..)
  , unionBranch, tsUnions
  -- *** Tagged
  , tagVal, taggedObject, taggedValue
  , TaggedBranches(..)
  , fmapTaggedBranches
  , Branch(..)
  , TaggedValueOpts(..)
  , taggedBranch
  , emptyTaggedBranch
  , tsTaggedUnion
  , tsTaggedUnions
  -- ** Intersections
  , IntersectVals(..)
  , intersectVal, tsIntersection
  -- ** Named
  , tsNamed, tsNamed_
  -- ** Generics
  , tsGeneric1
  , tsGeneric2
  , tsGeneric3
  -- , tsGeneric
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
  , tsEnumWith, tsEnumFrom, tsEnum
  , tsStringLit, tsNumericLit, tsIntegerLit, tsBigIntLit
  , tsUnknown, tsAny, tsVoid, tsUndefined, tsNull, tsNever
  -- * Printing
  , ppType
  , ppTypeF
  -- , typeExports
  -- , typeExports_
  -- , typeFExports
  -- , typeFExports_
  , IsInterface(..)
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
import           Data.Fin hiding                           (absurd)
import           Data.Functor.Apply
import           Data.Functor.Combinator
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divisible.Free
import           Data.Functor.Invariant
import           Data.HFunctor.Route
import           Data.Profunctor
import           Data.SOP                                  (NP(..), NS(..), I(..), K(..))
import           Data.Scientific
import           Data.Text                                 (Text)
import           Data.Traversable
import           GHC.TypeLits
import           Data.Type.Nat                             (Plus)
import           Data.Vec.Lazy                             (Vec)
import           Data.Void
import           Data.Kind
import           Typescript.Json.Core
import           Typescript.Json.Core.Combinators
import qualified Control.Applicative.Lift                  as Lift
import qualified Data.Aeson                                as A
import qualified Data.Aeson.BetterErrors                   as ABE
import qualified Data.Aeson.Encoding                       as AE
import qualified Data.ByteString                           as BS
import qualified Data.ByteString.Lazy                      as BSL
import qualified Data.Text                                 as T
import qualified Data.Text.Lazy                            as TL
import qualified Data.Type.Nat                             as Nat
import qualified Data.Vector.Generic                       as V
import qualified GHC.Exts                                  as Exts

-- | A type aggregating key-value pairs for an object.  Meant to
-- be assembled using 'keyVal' (for required properties) and 'keyValMay'
-- (for optional properties) and combined using its 'Applicative' instance.
-- To finally turn one into a 'TSType', use 'tsObject'.
--
-- In a @'ObjectProps' p n a b@, the @a@ represents the overall aggregate
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
-- myTypeProps :: 'ObjectProps' p n MyType MyType
-- myTypeProps = MyType
--   <$> 'keyVal' True mta "mta" ('TSType_' 'tsBoundedInteger')
--   <*> keyVal True mtb "mtb" (TSType_ 'tsBoolean')
--   <*> 'keyValMay' mtc "mtc" (TSType_ 'tsString')
--
-- myType :: TSType p 'IsObj n MyType
-- myType = tsObject myTypeProps
-- @
--
-- @
-- ppType myType
-- -- => { mta: number, mtb: boolean, mtc?: string }
-- @
--
-- In the above, @keyVal True mta "mta" tsBoundedInteger@ has the type
-- @ObjectProps p n MyType Int@, showing that it refers to the @Int@ field
-- of the @MyType@.  The trick to using this is to assemble 'ObjectProps'
-- together using Applicative combinators until the @a@ and @b@ "match",
-- and the 'ObjectProps' describes the entire value.  Then you can use
-- 'tsObject'.
newtype ObjectProps p n a b = ObjectProps
    { getObjectProps :: Ap (Pre a (ObjMember (TSType_ p n))) b }
  deriving newtype (Functor, Apply, Applicative)

instance Invariant (ObjectProps p n a) where
    invmap f _ = fmap f

instance Profunctor (ObjectProps p n) where
    dimap f g = ObjectProps . hmap (mapPre f) . fmap g . getObjectProps

-- | Create a single key-value pair for an object.  If the first argument
-- is 'True', will try to turn any nullable value (a value created using
-- 'tsNullable') into an optional property if possible.  Otherwise, always
-- uses a required property.
keyVal
    :: Bool             -- ^ turn nullable types into optional params if possible
    -> (a -> b)         -- ^ project this pair's value out of the aggregate type
    -> Text             -- ^ key (property name)
    -> TSType_ p n b
    -> ObjectProps p n a b
keyVal True f k (TSType_ (TSNullable t)) = ObjectProps . injectPre f $ ObjMember
    { objMemberKey = k
    , objMemberVal = R1 (hmap TSType_ t)
    }
keyVal _ f k t = ObjectProps . injectPre f $ ObjMember
    { objMemberKey = k
    , objMemberVal = L1 t
    }

-- | Create a single optional key-value pair for an object.
keyValMay
    :: (a -> Maybe b)   -- ^ project this pair's value out of the aggregate type, potentially revealing it is not present.
    -> Text             -- ^ key (property name)
    -> TSType_ p n b
    -> ObjectProps p n a (Maybe b)
keyValMay f k t = ObjectProps . injectPre f $ ObjMember
    { objMemberKey = k
    , objMemberVal = R1 (ilan t)
    }

-- | Gather together object properties into a 'TSType'.  See 'ObjectProps'
-- for details on how to use this.
tsObject
    :: ObjectProps p n a a
    -> TSType p 'IsObj n a
tsObject = TSObject . PreT . getObjectProps

-- | A type aggregating values in a tuple type.  Meant to
-- be assembled using 'tupleVal' and combined using its 'Applicative'
-- instance.  To finally turn one into a 'TSType', use 'tsTuple'.
--
-- In a @'TupleVals' p n a b@, the @a@ represents the overall aggregate
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
-- myTypeVals :: 'TupleVals' p n MyType MyType
-- myTypeVals = MyType
--   <$> 'tupleVal' mta (TSType_ 'tsBoundedInteger')
--   <*> tupleVal mtb (TSType_ 'tsBoolean')
--   <*> tupleVal mtc (TSType_ 'tsString')
--
-- myType :: TSType p 'NotObj n MyType
-- myType = tsTuple myTypeVals
-- @
--
-- @
-- ppType myType
-- -- => [number, boolean, string]
-- @
--
-- In the above, @tupleVal mta tsBoundedInteger@ has the type
-- @TupleVals p n MyType Int@, showing that it refers to the @Int@ field
-- of the @MyType@.  The trick to using this is to assemble 'TupleVals'
-- together using Applicative combinators until the @a@ and @b@ "match",
-- and the 'TupleVals' describes the entire value.  Then you can use
-- 'tsTuple'.
--
-- Note that the order that the 'Applicative' combination matters: it
-- determines the ordering of the tuple.
newtype TupleVals p n a b = TupleVals
    { getTupleVals :: Ap (Pre a (TSType_ p n)) b }
  deriving newtype (Functor, Apply, Applicative)

instance Invariant (TupleVals p n a) where
    invmap f _ = fmap f

instance Profunctor (TupleVals p n) where
    dimap f g = TupleVals . hmap (mapPre f) . fmap g . getTupleVals

-- | Create a singleton 'TupleVals', to be combined with applicative
-- combinators with others.
tupleVal
    :: (a -> b)         -- ^ project this pair's value out of the aggregate type
    -> TSType_ p n b
    -> TupleVals p n a b
tupleVal f = TupleVals . injectPre f

-- | Gather together tuple values into a 'TSType'.  See 'TupleVals' for
-- details on how to use this.
tsTuple
    :: TupleVals p n a a
    -> TSType p 'NotObj n a
tsTuple = TSTuple . PreT . getTupleVals

-- | A type aggregating branches in a union type.  Meant to
-- be assembled using 'unionBranch' and combined using its 'Decide'
-- instance.  To finally turn one into a 'TSType', use 'tsUnion'.
--
-- In a @'UnionBranches' p n a b@, the @a@ represents the overall aggregate
-- type, and the @b@ represents the type of the part that this
-- 'UnionBranches'
-- is describing.
--
-- @
-- data MyType = MTA Int | MTB Bool
--
-- myTypeBranches :: UnionBranches p n MyType MyType
-- myTypeBranches = 'decide' (\case MTA i -> Left i; MTB b -> Right b)
--     ('unionBranch' MTA (TSType_ 'tsBoundedInteger'))
--     ('unionBranch' MTB (TSType_ 'tsBoolean'))
--
-- myType :: TSType p 'NotObj n MyType
-- myType = tsUnion myTypeBranches
-- @
--
-- @
-- ppType myType
-- -- => number | boolean
-- @
--
-- In the above, @tupleVal mta tsBoundedInteger@ has the type
-- @UnionBranches p n MyType Int@, showing that it refers to the @Int@ field
-- of the @MyType@.  The trick to using this is to assemble 'UnionBranches'
-- together using Decide combinators until the @a@ and @b@ "match",
-- and the 'UnionBranches' describes the entire value.  Then you can use
-- 'tsUnion'.
--
-- Note that 'Decide' combinators can be a bit tedious to use if you have
-- a large number of branches.  'tsUnions' is an alternative to decide
-- combinators that uses heterogeneous lists, which can potentially make
-- things cleaner.
newtype UnionBranches p n a b = UnionBranches
    { getUnionBranches :: Dec (Post a (TSType_ p n)) b }
  deriving newtype (Contravariant, Decide, Conclude, Invariant)

-- | Create a singleton 'UnionBranches', to be combined with 'Decide'
-- combinators with others.  Can also be used with 'tsUnions' if you want
-- to combine a large number.
unionBranch
    :: (b -> a)                     -- ^ Embed the value into the main type
    -> TSType_ p n b
    -> UnionBranches p n a b
unionBranch f = UnionBranches . injectPost f

-- | Build up a union type from a collection of 'unionBranch's.  See
-- documentation for 'UnionBranches' for more information on how to use
-- this.
tsUnion
    :: UnionBranches p n a a
    -> TSType p 'NotObj n a
tsUnion = TSUnion . PostT . getUnionBranches

-- | A convenient way to combine multiple unions using 'NP' and 'NS'.
-- Takes a function to "break" the final type into each branch ('NS') and a tuple
-- ('NP') to handle each branch.
--
-- @
-- data MyType = MTA Int | MTB Bool | MTC String | MTD Double
--
-- subtypes :: NP (Dec (Post MyType (TSType_ p n)) '[Int, Bool, String, Double]
-- subtypes = 'unionBranch' MTA (TSType_ 'tsBoundedInteger')
--         ':*' unionBranch MTB (TSType_ 'tsBoolean')
--         :* unionBranch MTC (TSType_ 'tsString')
--         :* unionBranch MTD (TSType_ 'tsDouble')
--         :* 'Nil'
--
-- myType :: TSType p 'NotObj n MyType
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
tsUnions
    :: (a -> NS I as)
    -> NP (UnionBranches p n a) as
    -> TSType p 'NotObj n a
tsUnions f = tsUnion . contramap f . concludeN

data Branch p n a = Branch
    { branchTag   :: Text
    , branchType  :: Lift (TSType_ p n) a
    }

instance Invariant (Branch p n) where
    invmap f g (Branch a b) = Branch a (invmap f g b)

-- | A high-level data type describing the common pattern of a "tagged"
-- union (sum types in Haskell), where each branch comes in the form of an
-- object with a "tag" property with a string literal singleton, and the
-- rest of the object is the contents.  We would store an @Either Int Bool@ as, say,
-- @{ tag: "Left", contents: number } | { tag: "Right", contents: boolean }@.
--
-- Meant to be constructed using 'taggedBranch' and other 'Decide'
-- combinators.
newtype TaggedBranches p n a b = TaggedBranches
    { getTaggedBranches :: Dec (Post a (Branch p n)) b }
  deriving newtype (Contravariant, Decide, Conclude, Invariant)

fmapTaggedBranches :: (a -> c) -> TaggedBranches p n a b -> TaggedBranches p n c b
fmapTaggedBranches f = TaggedBranches . hmap (mapPost f) . getTaggedBranches

-- | Create a singleton 'TaggedBranches', to be combined with 'Decide'
-- combinators with others.  Can also be used with 'tsUnions' if you want
-- to combine a large number.
taggedBranch
    :: (b -> a)         -- ^ Embed the value into the main type
    -> Text             -- ^ Tag value
    -> TSType_ p n b
    -> TaggedBranches p n a b
taggedBranch f v = TaggedBranches . injectPost f . Branch v . Lift.Other

emptyTaggedBranch
    :: a                -- ^ the value of the main type that this branch represents
    -> Text             -- ^ Tag value
    -> TaggedBranches p n a ()
emptyTaggedBranch x v = TaggedBranches . injectPost (const x) $ Branch v (Lift.Pure ())

tsTaggedUnion
    :: TaggedValueOpts
    -> TaggedBranches p n a a
    -> TSType p 'NotObj n a
tsTaggedUnion tvo = tsUnion . runTaggedBranches tvo

tsTaggedUnions
    :: TaggedValueOpts
    -> (a -> NS I as)
    -> NP (TaggedBranches p n a) as
    -> TSType p 'NotObj n a
tsTaggedUnions tvo f = tsUnions f . hmap (runTaggedBranches tvo)

runTaggedBranches
    :: TaggedValueOpts
    -> TaggedBranches p n a b
    -> UnionBranches p n a b
runTaggedBranches tvo = UnionBranches
                      . hmap (hmap (runBranch tvo))
                      . getTaggedBranches

runBranch
    :: TaggedValueOpts
    -> Branch p n a
    -> TSType_ p n a
runBranch tvo Branch{..} = TSType_ $
  case branchType of
    Lift.Pure  x -> invmap (const x) (const ()) . tsObject $ tagVal (tvoTagKey tvo) branchTag
    Lift.Other t -> taggedValue tvo branchTag t


data TaggedValueOpts = TaggedValueOpts
    { tvoMergeTagValue :: Bool
    , tvoMergeNullable :: Bool
    , tvoTagKey        :: Text
    , tvoContentsKey   :: Text
    }
  deriving (Show, Eq, Ord)

instance Default TaggedValueOpts where
    def = TaggedValueOpts
        { tvoMergeTagValue = False
        , tvoMergeNullable = True
        , tvoTagKey = "tag"
        , tvoContentsKey = "contents"
        }

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
    -> ObjectProps p n a ()
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
    -> TSType p 'IsObj n a    -- ^ contents (object)
    -> TSType p 'IsObj n a
taggedObject tag val obj = tsIntersection $
       intersectVal (const ()) (tsObject (tagVal tag val))
    *> intersectVal id         obj

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
-- case1 :: TSType_ p n (Text, Int)
-- case1 = 'TSType_' . 'tsObject' $
--   (,) <$> 'keyVal' True "name" fst (TSType_ 'tsText')
--       <*> 'keyVal' True "age" snd (TSType_ 'tsBoundedInteger')
--
-- case2 :: TSType_ p n (Maybe Int)
-- case2 = 'TSType_' $ 'tsNullable' ('TSType_' 'tsBoundedInteger')
--
-- case3 :: TSType_ p n String
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
    -> TSType_ p n a   -- ^ contents type
    -> TSType p 'IsObj n a
taggedValue TaggedValueOpts{..} tagValue t
  | tvoMergeTagValue = case decideTSType_ t of
      L1 x -> tsObject $
           tagVal tvoTagKey tagValue
        *> keyVal tvoMergeNullable id tvoContentsKey (TSType_ x)
      R1 y -> taggedObject tvoTagKey tagValue y
  | otherwise        = tsObject $
         tagVal tvoTagKey tagValue
      *> keyVal tvoMergeNullable id tvoContentsKey t

-- | A type aggregating the parts of an intersection.  Meant to be
-- assembled using 'intersectVal' and combined using its 'Applicative'
-- instance.  To finally turn one into a 'TSType', use 'tsIntersection'.
--
-- In a @'IntersectVals' p n a b@, the @a@ represents the overall aggregate
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
-- myType :: TSType p 'IsObj n MyType
-- myType = tsObject $ MyType
--   <$> 'keyVal' True mta "mta" ('TSType_' 'tsBoundedInteger')
--   <*> keyVal True mtb "mtb" (TSType_ 'tsBoolean')
--   <*> 'keyValMay' mtc "mtc" (TSType_ 'tsString')
--
-- -- { tag: "something" }
-- tagType :: TSType p 'IsObj n ()
-- tagType = tagVal "tag" "something"
--
-- myTaggedType :: IntersectVals p n MyType MyType
-- myTaggedType = intersectVal tagType
--             *> intersectVal myType
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
newtype IntersectVals p n a b = IntersectVals
    { getIntersectVals :: Ap (Pre a (TSType p 'IsObj n)) b }
  deriving newtype (Functor, Apply, Applicative)

instance Invariant (IntersectVals p n a) where
    invmap f _ = fmap f

instance Profunctor (IntersectVals p n) where
    dimap f g = IntersectVals . hmap (mapPre f) . fmap g . getIntersectVals

-- | Create a singleton 'IntersectVals', to be combined with applicative
-- combinators with others.
--
-- Note that the input type must an object literal, indicated by @''IsObj'@
intersectVal
    :: (a -> b)
    -> TSType p 'IsObj n b
    -> IntersectVals p n a b
intersectVal f = IntersectVals . injectPre f

-- | Gather together intersection values into a 'TSType'.  See
-- 'IntersectionVals' for details on how to use this.
tsIntersection
    :: IntersectVals p n a a
    -> TSType p 'IsObj n a
tsIntersection = TSIntersection . PreT . getIntersectVals

-- | Wrap a type in a name, in a way that preserves @k@ (whether or not the
-- type is an object literal).
tsNamed
    :: Text
    -> TSType p k n a
    -> TSType p k n a
tsNamed nm t = TSNamedType (TSNamed
    { tsnName = nm
    , tsnType = TSNFunc (TSGeneric Nil (\n _ -> tsShift n t))
    }) Nil
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
    -> TSType_ p n a
    -> TSType_ p n a
tsNamed_ t = mapTSType_ (tsNamed t)

-- | Create a single-argument generic (parameterized) type.
--
-- For example, we could make a type imitating 'Maybe' in Haskell:
--
-- @
-- mkMaybe :: TSType_ p n a -> TSType_ p n (Maybe a)
-- mkMaybe = tsUnion $ decide (maybe (Left ()) Right) $
--     (tsTagged
-- @
tsGeneric1
    :: Text                     -- ^ Name of the type
    -> SIsObjType k             -- ^ Whether or not the type is an object literal.  Must be statically known.
    -> Text                     -- ^ Name of the parameter (used for printing)
    -> (forall r. SNat_ r -> TSType_ (Plus r p) n a -> TSType (Plus r p) k n b)         -- ^ Make a type, given the type parameter
    -> TSNamed p k n '[a] b
tsGeneric1 n o p f = TSNamed
    { tsnName = n
    , tsnType = TSNFunc $ TSGeneric (K p :* Nil) (\rs (t :* Nil) -> f rs t)
    }

tsGeneric2
    :: Text
    -> SIsObjType k
    -> Text
    -> Text
    -> (forall r. SNat_ r -> TSType_ (Plus r p) n a -> TSType_ (Plus r p) n b -> TSType (Plus r p) k n c)
    -> TSNamed p k n '[a, b] c
tsGeneric2 n o p q f = TSNamed
    { tsnName = n
    , tsnType = TSNFunc $
        TSGeneric (K p :* K q :* Nil) (\rs (t :* u :* Nil) -> f rs t u)
    }

tsGeneric3
    :: Text
    -> SIsObjType k
    -> Text
    -> Text
    -> Text
    -> (forall r. SNat_ r -> TSType_ (Plus r p) n a -> TSType_ (Plus r p) n b -> TSType_ (Plus r p) n c -> TSType (Plus r p) k n d)
    -> TSNamed p k n '[a, b, c] d
tsGeneric3 n o p q r f = TSNamed
    { tsnName = n
    , tsnType = TSNFunc $
        TSGeneric (K p :* K q :* K r :* Nil) (\rs (t :* u :* v :* Nil) -> f rs t u v)
    }

-- -- | A parameterized type with multiple parameters.  Prefer
-- tsGeneric
--     :: Text                 -- ^ Name
--     -> SIsObjType k         -- ^ whether or not it is an object literal
--     -> NP (K Text) as       -- ^ Name of parameters
--     -> (forall r. SNat_ r -> NP (TSType_ (Plus r p) n) as -> TSType (Plus r p) k n b)   -- ^ Type function
--     -> TSTypeF p k n as b
-- tsGeneric = TSGeneric

tsApplied
    :: TSNamed p k n as b
    -> NP (TSType_ p n) as
    -> TSType p k n b
tsApplied = TSNamedType

tsApply2
    :: TSNamed p k n '[a, b] c      -- ^ type function
    -> TSType_ p n a                -- ^ thing to apply
    -> TSType_ p n b                -- ^ thing to apply
    -> TSType p k n c
tsApply2 (TSNamed _ (TSNFunc (TSGeneric _ f))) tx ty = f SZ_ (tx :* ty :* Nil)
tsApply2 (TSNamed _ (TSNFunc (TSGenericInterface _ f))) tx ty = TSObject $ f SZ_ (tx :* ty :* Nil)

tsApply3
    :: TSNamed p k n '[a, b, c] d      -- ^ type function
    -> TSType_ p n a                   -- ^ thing to apply
    -> TSType_ p n b                   -- ^ thing to apply
    -> TSType_ p n c                   -- ^ thing to apply
    -> TSType p k n d
tsApply3 (TSNamed _ (TSNFunc (TSGeneric _ f))) tx ty tz = f SZ_ (tx :* ty :* tz :* Nil)
tsApply3 (TSNamed _ (TSNFunc (TSGenericInterface _ f))) tx ty tz = TSObject $ f SZ_ (tx :* ty :* tz :* Nil)

tsApplied1
    :: TSNamed p k n '[a] b
    -> TSType_ p n a
    -> TSType p k n b
tsApplied1 tf tx = tsApplied tf (tx :* Nil)

tsApplied2
    :: TSNamed p k n '[a, b] c
    -> TSType_ p n a
    -> TSType_ p n b
    -> TSType p k n c
tsApplied2 tf tx ty = tsApplied tf (tx :* ty :* Nil)

tsApplied3
    :: TSNamed p k n '[a, b, c] d
    -> TSType_ p n a
    -> TSType_ p n b
    -> TSType_ p n c
    -> TSType p k n d
tsApplied3 tf tx ty tz = tsApplied tf (tx :* ty :* tz :* Nil)

tsList :: TSType_ p n a -> TSType p 'NotObj n [a]
tsList = withTSType_ (TSArray . ilan)

tsVector :: V.Vector v a => TSType_ p n a -> TSType p 'NotObj n (v a)
tsVector = invmap V.fromList V.toList . tsList

tsIsList :: Exts.IsList l => TSType_ p n (Exts.Item l) -> TSType p 'NotObj n l
tsIsList = invmap Exts.fromList Exts.toList . tsList

tsNullable :: TSType_ p n a -> TSType p 'NotObj n (Maybe a)
tsNullable = withTSType_ (TSNullable . ilan)

tsBoolean :: TSType p 'NotObj n Bool
tsBoolean = TSPrimType $ inject TSBoolean

tsNumber :: TSType p 'NotObj n Scientific
tsNumber = TSPrimType $ inject TSNumber

tsBoundedInteger :: (Integral a, Bounded a) => TSType p 'NotObj n a
tsBoundedInteger = TSPrimType $ PS TSNumber
    (\x -> case toBoundedInteger x of
            Nothing -> Left . T.pack $ "Not an integer: " <> show x
            Just i  -> Right i
    ) fromIntegral

tsInteger :: Integral a => TSType p 'NotObj n a
tsInteger = TSPrimType $ PS TSNumber
    (\x -> first (\n -> T.pack $ "Not an integer: " <> show @Double n) (floatingOrInteger x))
    fromIntegral

tsRealFloat :: RealFloat a => TSType p 'NotObj n a
tsRealFloat = invmap toRealFloat fromFloatDigits tsNumber

tsDouble :: TSType p 'NotObj n Double
tsDouble = tsRealFloat

tsBigInt :: TSType p 'NotObj n Integer
tsBigInt = TSPrimType $ inject TSBigInt

tsText :: TSType p 'NotObj n Text
tsText = TSPrimType $ inject TSString

tsLazyText :: TSType p 'NotObj n TL.Text
tsLazyText = invmap TL.fromStrict TL.toStrict tsText

tsString :: TSType p 'NotObj n String
tsString = invmap T.unpack T.pack tsText

tsEnumWith :: Text -> Vec m (Text, EnumLit) -> TSType p 'NotObj n (Fin m)
tsEnumWith nm xs = TSNamedType (TSNamed nm (TSNPrimType (inject (TSEnum xs)))) Nil

tsEnum :: Text -> Vec m Text -> TSType p 'NotObj n (Fin m)
tsEnum nm = tsEnumFrom nm 0

tsEnumFrom :: Text -> Int -> Vec m Text -> TSType p 'NotObj n (Fin m)
tsEnumFrom nm i0 xs = tsEnumWith nm xs'
  where
    xs' = flip evalState i0 . for xs $ \x -> state $ \i ->
      ((x, ELNumber (fromIntegral i)), i+1)

tsStringLit :: Text -> TSType p 'NotObj n ()
tsStringLit = TSPrimType . inject . TSStringLit

tsNumericLit :: Scientific -> TSType p 'NotObj n ()
tsNumericLit = TSPrimType . inject . TSNumericLit

tsIntegerLit :: Integral a => a -> TSType p 'NotObj n ()
tsIntegerLit = TSPrimType . inject . TSNumericLit . fromIntegral

tsBigIntLit :: Integer -> TSType p 'NotObj n ()
tsBigIntLit = TSPrimType . inject . TSBigIntLit

tsUnknown :: TSType p 'NotObj n A.Value
tsUnknown = TSPrimType $ inject TSUnknown

tsAny :: TSType p 'NotObj n A.Value
tsAny = TSPrimType $ inject TSAny

tsVoid :: TSType p 'NotObj n ()
tsVoid = TSPrimType $ inject TSVoid

tsUndefined :: TSType p 'NotObj n ()
tsUndefined = TSPrimType $ inject TSUndefined

tsNull :: TSType p 'NotObj n ()
tsNull = TSPrimType $ inject TSNull

tsNever :: TSType p 'NotObj n Void
tsNever = TSPrimType $ inject TSNever

encodeType :: TSType 'Nat.Z k Void a -> a -> BSL.ByteString
encodeType t = AE.encodingToLazyByteString . typeToEncoding t

encodeTypeStrict :: TSType 'Nat.Z k Void a -> a -> BS.ByteString
encodeTypeStrict t = BSL.toStrict . encodeType t

decodeType
    :: TSType 'Nat.Z k Void a
    -> BSL.ByteString
    -> Either (ABE.ParseError ParseErr) a
decodeType t = ABE.parse (parseType t)

decodeTypeStrict
    :: TSType 'Nat.Z k Void a
    -> BS.ByteString
    -> Either (ABE.ParseError ParseErr) a
decodeTypeStrict t = ABE.parseStrict (parseType t)

