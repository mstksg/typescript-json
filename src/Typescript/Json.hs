{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE EmptyCase        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module Typescript.Json (
    keyVal, keyValMay, tsObject
  , tupleVal, tsTuple
  , unionVal, tsUnions
  , tsList, tsVector, tsIsList
  , tsBoolean
  , tsNumber, tsBoundedInteger, tsInteger, tsRealFloat, tsDouble, tsBigInt
  , tsText, tsString
  , tsEnumWith, tsEnumFrom, tsEnum
  , tsStringLit, tsNumericLit, tsIntegerLit, tsBigIntLit
  , tsUnknown, tsAny, tsVoid, tsUndefined, tsNull, tsNever
  ) where

import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Fin
import           Data.Functor.Combinator
import           Data.Functor.Contravariant.Divisible.Free
import           Data.Functor.Invariant
import           Data.HFunctor.Route
import           Data.SOP                                  (NP(..), NS(..), I(..))
import           Data.Scientific
import           Data.Text                                 (Text)
import           Data.Traversable
import           Data.Vec.Lazy                             (Vec)
import           Data.Void
import           GHC.Generics
import           Typescript.Json.Core
import           Typescript.Json.Core.Combinators
import qualified Data.Aeson                                as A
import qualified Data.SOP                                  as SOP
import qualified Data.Text                                 as T
import qualified Data.Vector.Generic                       as V
import qualified GHC.Exts                                  as Exts

keyVal
    :: (a -> b)
    -> Text
    -> TSType_ ps n b
    -> Ap (Pre a (ObjMember (TSType_ ps n))) b
keyVal f k t = injectPre f $ ObjMember
    { objMemberKey = k
    , objMemberVal = L1 t
    }

keyValMay
    :: (a -> Maybe b)
    -> Text
    -> TSType_ ps n b
    -> Ap (Pre a (ObjMember (TSType_ ps n))) (Maybe b)
keyValMay f k t = injectPre f $ ObjMember
    { objMemberKey = k
    , objMemberVal = R1 (ilan t)
    }

tsObject
    :: Ap (Pre a (ObjMember (TSType_ ps n))) a
    -> TSType ps 'IsObj n a
tsObject = TSObject . PreT

tupleVal
    :: (a -> b)
    -> TSType_ ps n b
    -> Ap (Pre a (TSType_ ps n)) b
tupleVal = injectPre

tsTuple
    :: Ap (Pre a (TSType_ ps n)) a
    -> TSType ps 'NotObj n a
tsTuple = TSTuple . PreT

unionVal
    :: (b -> a)
    -> TSType_ ps n b
    -> Dec (Post a (TSType_ ps n)) b
unionVal = injectPost

tsUnion
    :: Dec (Post a (TSType_ ps n)) a
    -> TSType ps 'NotObj n a
tsUnion = TSUnion . PostT

tsUnions
    :: NP (TSType_ ps n) as
    -> TSType ps 'NotObj n (NS I as)
tsUnions = tsUnion . concludeN . imapNP (\i -> injectPost @Dec (i . I))

imapNP
    :: (forall x. (forall g. g x -> NS g as) -> f x -> h x)
    -> NP f as
    -> NP h as
imapNP f = \case
    Nil     -> Nil
    x :* xs -> f Z x :* imapNP (\q -> f (S . q)) xs

tsList :: TSType_ ps n a -> TSType_ ps n [a]
tsList = withTSType_ (TSType_ . TSArray . ilan)

tsVector :: V.Vector v a => TSType_ ps n a -> TSType_ ps n (v a)
tsVector = invmap V.fromList V.toList . tsList

tsIsList :: Exts.IsList l => TSType_ ps n (Exts.Item l) -> TSType_ ps n l
tsIsList = invmap Exts.fromList Exts.toList . tsList

tsBoolean :: TSType ps 'NotObj n Bool
tsBoolean = TSPrimType $ inject TSBoolean

tsNumber :: TSType ps 'NotObj n Scientific
tsNumber = TSPrimType $ inject TSNumber

tsBoundedInteger :: (Integral a, Bounded a) => TSType ps 'NotObj n a
tsBoundedInteger = TSPrimType $ PS TSNumber
    (\x -> case toBoundedInteger x of
            Nothing -> Left . T.pack $ "Not an integer: " <> show x
            Just i  -> Right i
    ) fromIntegral

tsInteger :: Integral a => TSType ps 'NotObj n a
tsInteger = TSPrimType $ PS TSNumber
    (\x -> first (\n -> T.pack $ "Not an integer: " <> show @Double n) (floatingOrInteger x))
    fromIntegral

tsRealFloat :: RealFloat a => TSType ps 'NotObj n a
tsRealFloat = invmap toRealFloat fromFloatDigits tsNumber

tsDouble :: TSType ps 'NotObj n Double
tsDouble = tsRealFloat

tsBigInt :: TSType ps 'NotObj n Integer
tsBigInt = TSPrimType $ inject TSBigInt

tsText :: TSType ps 'NotObj n Text
tsText = TSPrimType $ inject TSString

tsString :: TSType ps 'NotObj n String
tsString = invmap T.unpack T.pack tsText

tsEnumWith :: Text -> Vec m (Text, EnumLit) -> TSType ps 'NotObj n (Fin m)
tsEnumWith nm xs = TSPrimType $ inject (TSEnum nm xs)

tsEnum :: Text -> Vec m Text -> TSType ps 'NotObj n (Fin m)
tsEnum nm = tsEnumFrom nm 0

tsEnumFrom :: Text -> Int -> Vec m Text -> TSType ps 'NotObj n (Fin m)
tsEnumFrom nm i0 xs = tsEnumWith nm xs'
  where
    xs' = flip evalState i0 . for xs $ \x -> state $ \i ->
      ((x, ELNumber (fromIntegral i)), i+1)

tsStringLit :: Text -> TSType ps 'NotObj n ()
tsStringLit = TSPrimType . inject . TSStringLit

tsNumericLit :: Scientific -> TSType ps 'NotObj n ()
tsNumericLit = TSPrimType . inject . TSNumericLit

tsIntegerLit :: Integral a => a -> TSType ps 'NotObj n ()
tsIntegerLit = TSPrimType . inject . TSNumericLit . fromIntegral

tsBigIntLit :: Integer -> TSType ps 'NotObj n ()
tsBigIntLit = TSPrimType . inject . TSBigIntLit

tsUnknown :: TSType ps 'NotObj n A.Value
tsUnknown = TSPrimType $ inject TSUnknown

tsAny :: TSType ps 'NotObj n A.Value
tsAny = TSPrimType $ inject TSAny

tsVoid :: TSType ps 'NotObj n ()
tsVoid = TSPrimType $ inject TSVoid

tsUndefined :: TSType ps 'NotObj n ()
tsUndefined = TSPrimType $ inject TSUndefined

tsNull :: TSType ps 'NotObj n ()
tsNull = TSPrimType $ inject TSNull

tsNever :: TSType ps 'NotObj n Void
tsNever = TSPrimType $ inject TSNever

