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

module Typescript.Json.Union (
  -- * Unions
    tsUnion, tsUnions
  -- ** Tagged
  , tagVal, taggedObject, taggedValue, taggedNullary
  , TaggedBranches(..)
  , Branch(..)
  , TaggedValueOpts(..)
  , taggedBranch
  , mergeTB
  , emptyTaggedBranch
  , tsTaggedUnion
  , tsTaggedUnions
  -- * Misc
  , tsMaybe
  ) where

import           Data.Default.Class
import           Data.Functor.Apply
import           Data.Functor.Combinator
import           Data.Functor.Contravariant
import           Data.Functor.Invariant
import           Data.Functor.Invariant.DecAlt
import           Data.SOP                             (NP(..), NS(..), I(..))
import           Data.Text                            (Text)
import           Typescript.Json.Collection
import           Typescript.Json.Primitive
import           Typescript.Json.Types
import qualified Control.Applicative.Lift             as Lift
import qualified Data.Set                             as S


-- | Build up a union type from a 'unionBranch'.
tsUnion
    :: TSUnionBranches p a
    -> TSType p 'NotObj a
tsUnion = TSUnion

-- TODO: this is all wrong

-- | A convenient way to combine multiple unions using 'NP' and 'NS'.
-- Takes a function to "break" the final type into each branch ('NS') and a tuple
-- ('NP') to handle each branch.
--
-- @
-- data MyType = MTA Int | MTB Bool | MTC String | MTD Double
--
-- subtypes :: NP (TSUnionBranches p) '[Int, Bool, String, Double]
-- subtypes = 'tsBranchUnions' (TSType_ 'tsBoundedInteger')
--         ':*' tsBranchUnions (TSType_ 'tsBoolean')
--         :* tsBranchUnions (TSType_ 'tsString')
--         :* tsBranchUnions (TSType_ 'tsDouble')
--         :* 'Nil'
--
-- myType :: TSType p 'NotObj MyType
-- myType = tsUnions splitMyType embedMyType subtypes
--   where
--     splitMyType = \case
--       MTA i -> Z (I i)
--       MTB b -> S (Z (I b))
--       MTC s -> S (S (S (I s)))
--       MTA d -> S (S (S (S (I d))))
--     embedMyType =
--          'Op' MTA
--       :* Op MTB
--       :* Op MTC
--       :* Op MTD
--       :* Nil
-- @
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
    , tacTagReadOnly   :: Mutability
    , tacContentsReadOnly :: Mutability
    }
  deriving (Show, Eq, Ord)

data TagIsKey = TagIsKey
    { tikNullaryIsString :: Bool  -- ^ nullary constructors are just string literals. if False, they are { tag: null }.
    , tikReadOnly        :: Mutability
    }
  deriving (Show, Eq, Ord)

instance Default TagAndContents where
    def = TagAndContents
        { tacMergeTagValue = False
        , tacTagKey = "tag"
        , tacContentsKey = "contents"
        , tacTagReadOnly = ReadOnly
        , tacContentsReadOnly = Mutable
        }

instance Default TagIsKey where
    def = TagIsKey
        { tikNullaryIsString = True
        , tikReadOnly = ReadOnly
        }

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
    :: Mutability   -- ^ readonly
    -> Text         -- ^ tag key
    -> Text         -- ^ tag value
    -> ObjectProps p a ()
tagVal ro tag val = keyVal False (const ()) ro tag $ TSType_ (tsStringLit val)

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
    :: Mutability           -- ^ readonly
    -> Text                 -- ^ tag key
    -> Text                 -- ^ tag value
    -> TSType p 'IsObj a    -- ^ contents (object)
    -> TSType p 'IsObj a
taggedObject ro tag val obj = tsIntersection $
       intersectVal (const ()) (tsObject (tagVal ro tag val))
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
--   (,) \<$\> 'keyVal' True "name" fst (TSType_ 'tsText')
--       \<*\> 'keyVal' True "age" snd (TSType_ 'tsBoundedInteger')
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
          L1 x -> tsObject $ tagVal tacTagReadOnly tacTagKey tagValue
                          *> keyVal False id tacContentsReadOnly tacContentsKey (TSType_ x)
          R1 y
            -- TODO: if the tag key is a key in the obj, then dont do it
            | tacTagKey `S.member` isObjKeys y
                -> tsObject $ tagVal tacTagReadOnly tacTagKey tagValue
                           *> keyVal False id tacContentsReadOnly tacContentsKey t
            | otherwise -> taggedObject tacTagReadOnly tacTagKey tagValue y
      | otherwise -> tsObject $
             tagVal tacTagReadOnly tacTagKey tagValue
          *> keyVal False id tacContentsReadOnly tacContentsKey t
    TVOTagIsKey TagIsKey{..} -> tsObject $ keyVal False id tikReadOnly tagValue t

taggedNullary
    :: TaggedValueOpts
    -> Text
    -> a
    -> TSType_ p a
taggedNullary tvo tagValue x = invmap (const x) (const ()) $ case tvo of
    TVOTagAndContents TagAndContents{..} ->
        TSType_ $ tsObject (tagVal tacTagReadOnly tacTagKey tagValue)
    TVOTagIsKey TagIsKey{..}
      | tikNullaryIsString -> TSType_ $ tsStringLit tagValue
      | otherwise          -> TSType_ $ tsObject (keyVal False id tikReadOnly tagValue (TSType_ tsNull))

tsMaybe
    :: Text         -- ^ the "nothing" constructor
    -> Text         -- ^ the "just" field
    -> TSType_ p a
    -> TSType p 'NotObj (Maybe a)
tsMaybe n j t = tsTaggedUnions
    (TVOTagIsKey def)
    (\case Nothing -> Z (I ()); Just x -> S (Z (I x)))
    (Op (const Nothing) :* Op Just :* Nil)
    (  emptyTaggedBranch n ()
    :* taggedBranch j t
    :* Nil
    )


