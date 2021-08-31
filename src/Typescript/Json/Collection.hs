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

-- |
-- Module      : Typescript.Json.Collection
-- Copyright   : (c) Justin Le 2021
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Construct Typescript values for json collections, such as arrays,
-- tuples, and objects.
module Typescript.Json.Collection (
  -- * Lists and Nullables
    tsList, tsVector, tsIsList
  -- * Object
  , ObjectProps(..)
  , keyVal, keyValMay, tsObject
  -- * Tuple
  , TupleVals(..)
  , tupleVal, tsTuple
  , stripObjectVals
  -- ** Haskell Tuples
  , tsTuple2
  , tsTuple3
  , tsTuple4
  -- * Intersections
  , IntersectVals(..)
  , intersectVal, tsIntersection
  ) where

import           Control.Applicative.Free
import           Data.Functor.Apply
import           Data.Functor.Combinator
import           Data.Functor.Invariant
import           Data.HFunctor.Route
import           Data.Profunctor
import           Data.Text                         (Text)
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators
import qualified Data.Vector.Generic               as V
import qualified GHC.Exts                          as Exts

-- | Given a typescript @T@, returns a Typescript @T[]@ represented as
-- a Haskell lazily linked list.
tsList :: TSType_ p a -> TSType p 'NotObj [a]
tsList = withTSType_ (TSArray . ilan)

-- | Given a typescript @T@, returns a Typescript @T[]@ represented as
-- a Haskell vector from the vector library.
tsVector :: V.Vector v a => TSType_ p a -> TSType p 'NotObj (v a)
tsVector = invmap V.fromList V.toList . tsList

-- | Given a typescript @T@ of item values, returns a Typescript @Array<T>@
-- represented as any instance of 'Exts.IsList'.
--
-- For example, given a typescript representation of @(k, v)@, can return
-- a typescript representation of @'Map' k v@ (represented as a list of
-- key-value pairs) because of 'Map''s 'Exts.IsList' instance.
--
-- @
-- > let tsSTringIntMap :: 'TSType' p 'NotObj (Map String Int)
--       tsStringIntMap = 'tsIsList' $ 'TSType_' ('tsTuple2' (TSType_ 'tsString') (TSType_ 'tsInt'))
-- > 'ppType' tsStringIntMap
-- [ string, number ][]
-- > encodeType tsStringIntMap $ Map.fromList [("hi", 2), ("bye", 5), ("ok", 1)]
-- [["bye", 5], ["hi", 2], ["ok", 10]]
-- @
tsIsList :: Exts.IsList l => TSType_ p (Exts.Item l) -> TSType p 'NotObj l
tsIsList = invmap Exts.fromList Exts.toList . tsList

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
--   \<$\> 'keyVal' True mta "mta" ('TSType_' 'tsBoundedInteger')
--   \<*\> keyVal True mtb "mtb" (TSType_ 'tsBoolean')
--   \<*\> 'keyValMay' mtc "mtc" (TSType_ 'tsString')
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
    -> Mutability
    -> Text             -- ^ key (property name)
    -> TSType_ p b
    -> ObjectProps p a b
keyVal True f ro k (TSType_ t) = ObjectProps . injectPre f $ ObjMember
    { objMemberReadOnly = ro
    , objMemberKey = k
    , objMemberVal = case isNullable t of
        Nothing -> L1 $ TSType_ t
        Just u  -> R1 $ hmap TSType_ u
    }
keyVal False f ro k t = ObjectProps . injectPre f $ ObjMember
    { objMemberReadOnly = ro
    , objMemberKey = k
    , objMemberVal = L1 t
    }

-- | Create a single optional key-value pair for an object.
keyValMay
    :: (a -> Maybe b)   -- ^ project this pair's value out of the aggregate type, potentially revealing it is not present.
    -> Mutability
    -> Text             -- ^ key (property name)
    -> TSType_ p b
    -> ObjectProps p a (Maybe b)
keyValMay f ro k t = ObjectProps . injectPre f $ ObjMember
    { objMemberReadOnly = ro
    , objMemberKey = k
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
--   \<$\> 'tupleVal' mta (TSType_ 'tsBoundedInteger')
--   \<*\> tupleVal mtb (TSType_ 'tsBoolean')
--   \<*\> tupleVal mtc (TSType_ 'tsString')
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

-- | Pull together two types into a Haskell tuple, representing
-- a typescript 2-tuple.
--
-- @
-- tsTuple2 x y = tsTuple $
--     (,) <$> tupleVal fst x
--         <*> tupleVal snd y
-- @
--
-- @
-- > let stringIntTuple = 'ppType' $ 'tsTuple' ('TSType_' 'tsString') (TSType_ 'tsInt')
-- > 'ppType' stringIntTuple
-- [ string, number ]
-- > encodeType tsStringIntMap ("hi", 3)
-- [ "hi", 3 ]
-- @
tsTuple2
    :: TSType_ p a
    -> TSType_ p b
    -> TSType p 'NotObj (a, b)
tsTuple2 x y = tsTuple $
    (,) <$> tupleVal fst x
        <*> tupleVal snd y

-- | Pull together three types into a Haskell tuple, representing
-- a typescript 3-tuple.
tsTuple3
    :: TSType_ p a
    -> TSType_ p b
    -> TSType_ p c
    -> TSType p 'NotObj (a, b, c)
tsTuple3 x y z = tsTuple $
    (,,) <$> tupleVal (\(a,_,_) -> a) x
         <*> tupleVal (\(_,b,_) -> b) y
         <*> tupleVal (\(_,_,c) -> c) z

-- | Pull together four types into a Haskell tuple, representing
-- a typescript 4-tuple.
tsTuple4
    :: TSType_ p a
    -> TSType_ p b
    -> TSType_ p c
    -> TSType_ p d
    -> TSType p 'NotObj (a, b, c, d)
tsTuple4 x y z q = tsTuple $
    (,,,) <$> tupleVal (\(a,_,_,_) -> a) x
          <*> tupleVal (\(_,b,_,_) -> b) y
          <*> tupleVal (\(_,_,c,_) -> c) z
          <*> tupleVal (\(_,_,_,d) -> d) q


-- | Strip the keys from an 'ObjectProps' and turn it into just a plain
-- tuple.
--
-- For example, @{ hi: string, bye: number }@ turns into @[string,
-- number]@.
stripObjectVals :: ObjectProps p a b -> TupleVals p a b
stripObjectVals = TupleVals
                . hmap (hmap ((id !*! go) . objMemberVal))
                . getObjectProps
  where
    go (ILan f g (TSType_ x)) = TSType_ . invmap f g $ mkNullable x


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
--   \<$\> 'keyVal' True mta "mta" ('TSType_' 'tsBoundedInteger')
--   \<*\> keyVal True mtb "mtb" (TSType_ 'tsBoolean')
--   \<*\> 'keyValMay' mtc "mtc" (TSType_ 'tsString')
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

