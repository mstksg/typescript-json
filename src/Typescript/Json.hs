{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE EmptyCase        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

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
  , keyVal, keyValMay, tsObject
  -- ** Tuple
  , tupleVal, tsTuple
  -- ** Unions
  , unionVal, tsUnions
  , tagVal, taggedObject, taggedValue
  -- ** Intersections
  , intersectVal, tsIntersection
  -- ** Named
  , tsNamed, tsNamed_
  -- ** Generics
  , tsGeneric1
  , tsApplied1
  , tsApply1
  , tsGeneric
  , tsApplied
  , tsApply
  -- ** Primitives
  , tsBoolean
  , tsNumber, tsBoundedInteger, tsInteger, tsRealFloat, tsDouble, tsBigInt
  , tsText, tsString
  , tsEnumWith, tsEnumFrom, tsEnum
  , tsStringLit, tsNumericLit, tsIntegerLit, tsBigIntLit
  , tsUnknown, tsAny, tsVoid, tsUndefined, tsNull, tsNever
  -- * Printing
  , ppType
  , ppTypeF
  , typeExports
  , typeExports_
  , typeFExports
  , typeFExports_
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
import           Data.Fin hiding                           (absurd)
import           Data.Functor.Combinator
import           Data.Functor.Contravariant.Divisible.Free
import           Data.Functor.Invariant
import           Data.HFunctor.Route
import           Data.SOP                                  (NP(..), NS(..), I(..), K(..))
import           Data.Scientific
import           Data.Text                                 (Text)
import           Data.Traversable
import           Data.Type.Nat                             (Plus)
import           Data.Vec.Lazy                             (Vec)
import           Data.Void
import           Typescript.Json.Core
import           Typescript.Json.Core.Combinators
import qualified Data.Aeson                                as A
import qualified Data.Aeson.BetterErrors                   as ABE
import qualified Data.ByteString                           as BS
import qualified Data.ByteString.Lazy                      as BSL
import qualified Data.Text                                 as T
import qualified Data.Type.Nat                             as Nat
import qualified Data.Vector.Generic                       as V
import qualified GHC.Exts                                  as Exts

keyVal
    :: Bool             -- ^ turn nullable types into optional params if possible
    -> (a -> b)
    -> Text
    -> TSType_ p n b
    -> Ap (Pre a (ObjMember (TSType_ p n))) b
keyVal True f k (TSType_ (TSNullable t)) = injectPre f $ ObjMember
    { objMemberKey = k
    , objMemberVal = R1 (hmap TSType_ t)
    }
keyVal _ f k t = injectPre f $ ObjMember
    { objMemberKey = k
    , objMemberVal = L1 t
    }

keyValMay
    :: (a -> Maybe b)
    -> Text
    -> TSType_ p n b
    -> Ap (Pre a (ObjMember (TSType_ p n))) (Maybe b)
keyValMay f k t = injectPre f $ ObjMember
    { objMemberKey = k
    , objMemberVal = R1 (ilan t)
    }

tsObject
    :: Ap (Pre a (ObjMember (TSType_ p n))) a
    -> TSType p 'IsObj n a
tsObject = TSObject . PreT

tupleVal
    :: (a -> b)
    -> TSType_ p n b
    -> Ap (Pre a (TSType_ p n)) b
tupleVal = injectPre

tsTuple
    :: Ap (Pre a (TSType_ p n)) a
    -> TSType p 'NotObj n a
tsTuple = TSTuple . PreT

unionVal
    :: (b -> a)
    -> TSType_ p n b
    -> Dec (Post a (TSType_ p n)) b
unionVal = injectPost

tsUnion
    :: Dec (Post a (TSType_ p n)) a
    -> TSType p 'NotObj n a
tsUnion = TSUnion . PostT

tsUnions
    :: NP (TSType_ p n) as
    -> TSType p 'NotObj n (NS I as)
tsUnions = tsUnion . concludeN . imapNP (\i -> injectPost @Dec (i . I))

imapNP
    :: (forall x. (forall g. g x -> NS g as) -> f x -> h x)
    -> NP f as
    -> NP h as
imapNP f = \case
    Nil     -> Nil
    x :* xs -> f Z x :* imapNP (\q -> f (S . q)) xs

tagVal
    :: Text         -- ^ tag key
    -> Text         -- ^ tag value
    -> Ap (Pre a (ObjMember (TSType_ p n))) ()
tagVal tag val = keyVal False (const ()) tag $ TSType_ (tsStringLit val)

taggedObject
    :: Text                   -- ^ tag key
    -> Text                   -- ^ tag value
    -> TSType p 'IsObj n a   -- ^ contents (object)
    -> TSType p 'IsObj n a
taggedObject tag val obj = tsIntersection $
       intersectVal (const ()) (tsObject (tagVal tag val))
    *> intersectVal id         obj

taggedValue
    :: Bool                   -- ^ merge tag and value if possible
    -> Bool                   -- ^ treat nullable types as optional properties if possible
    -> Text                   -- ^ tag key
    -> Text                   -- ^ tag value
    -> Text                   -- ^ contents key
    -> TSType_ p n a   -- ^ contents (object)
    -> TSType p 'IsObj n a
taggedValue False nul tag val contents obj = tsObject $
         tagVal tag val
      *> keyVal nul id contents obj
taggedValue True  nul tag val contents obj = case decideTSType_ obj of
    L1 x -> tsObject $
         tagVal tag val
      *> keyVal nul id contents (TSType_ x)
    R1 y -> taggedObject tag val y

intersectVal
    :: (a -> b)
    -> TSType p 'IsObj n b
    -> Ap (Pre a (TSType p 'IsObj n)) b
intersectVal = injectPre

tsIntersection
    :: Ap (Pre a (TSType p 'IsObj n)) a
    -> TSType p 'IsObj n a
tsIntersection = TSIntersection . PreT

tsNamed
    :: Text
    -> TSType p k n a
    -> TSType p k n a
tsNamed = TSNamed

tsNamed_
    :: Text
    -> TSType_ p n a
    -> TSType_ p n a
tsNamed_ t = mapTSType_ (tsNamed t)

tsGeneric
    :: Text
    -> SIsObjType k
    -> NP (K Text) as
    -> (forall r. SNat_ r -> NP (TSType_ (Plus r p) n) as -> TSType (Plus r p) k n b)
    -> TSTypeF p k n as b
tsGeneric = TSGeneric

tsApplied
    :: TSTypeF p k n as b
    -> NP (TSType_ p n) as
    -> TSType p k n b
tsApplied = TSApplied

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

tsString :: TSType p 'NotObj n String
tsString = invmap T.unpack T.pack tsText

tsEnumWith :: Text -> Vec m (Text, EnumLit) -> TSType p 'NotObj n (Fin m)
tsEnumWith nm xs = TSPrimType $ inject (TSEnum nm xs)

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
encodeType t = A.encode . typeToValue t

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

