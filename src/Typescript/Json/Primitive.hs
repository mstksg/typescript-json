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

module Typescript.Json.Primitive (
  -- * Primitives
    tsBoolean
  , tsNumber, tsBoundedInteger, tsInteger, tsRealFloat, tsDouble, tsBigInt
  , tsText, tsLazyText, tsString
  , tsStringLit, tsNumericLit, tsIntegerLit, tsBigIntLit
  , tsUnknown, tsAny, tsVoid, tsUndefined, tsNull, tsNever
  ) where

import           Data.Bifunctor
import           Data.Functor.Combinator
import           Data.Functor.Invariant
import           Data.Scientific
import           Data.Text                         (Text)
import           Data.Void
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators
import qualified Data.Aeson                        as A
import qualified Data.Text                         as T
import qualified Data.Text.Lazy                    as TL


tsBoolean :: TSType p 'NotObj Bool
tsBoolean = TSBaseType $ inject TSBoolean

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
tsStringLit = TSBaseType . inject . TSStringLit

tsNumericLit :: Scientific -> TSType p 'NotObj ()
tsNumericLit = TSBaseType . inject . TSNumericLit

tsIntegerLit :: Integral a => a -> TSType p 'NotObj ()
tsIntegerLit = TSBaseType . inject . TSNumericLit . fromIntegral

tsBigIntLit :: Integer -> TSType p 'NotObj ()
tsBigIntLit = TSBaseType . inject . TSBigIntLit

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

