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
-- Module      : Typescript.Json.Primitive
-- Copyright   : (c) Justin Le 2021
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Construct Typescript values for json primitive values.
--
-- Typically you would make these and then assemble them with compound
-- combinators like in "Typescript.Json.Collection" and
-- "Typescript.Json.Union".  If you want to use them directly, you can use
-- 'invmap' to totally convert the raw types ('Bool', 'Int', etc.) into the
-- types you want.
--
-- To parse arbitrary json 'A.Value' as an arbitrary type with errors, use
-- 'tsAnyWith' and 'tsUnknownWith' and its variants.  These are represented
-- in typescript as @any@ and @unknown@, respectively.
module Typescript.Json.Primitive (
  -- * Simple
    tsBoolean
  , tsVoid
  , tsUndefined
  , tsNull
  , tsNever
  -- * Numeric
  , tsNumber
  , tsBoundedInteger
  , tsInteger
  , tsRealFloat
  , tsDouble
  , tsInt
  , tsBigInt
  -- * String
  , tsText
  , tsLazyText
  , tsString
  -- * Literals
  , tsStringLit
  , tsNumericLit
  , tsIntegerLit
  , tsBigIntLit
  -- ** Type-Directed
  , SSymbol(..), tsStringLitSymbol
  , SNat(..), tsIntegerLitNat, tsBigIntLitNat
  -- * Open
  , tsAny
  , tsUnknown
  -- ** Arbitrary
  , tsAnyWith
  , tsUnknownWith
  -- ** From aeson typeclasses
  , tsAesonAny
  , tsAesonUnknown
  ) where

import           Data.Bifunctor
import           Data.Functor.Combinator
import           Data.Functor.Invariant
import           Data.Scientific
import           Data.Text                         (Text)
import           Data.Void
import           GHC.TypeLits
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators
import qualified Data.Aeson                        as A
import qualified Data.Text                         as T
import qualified Data.Text.Lazy                    as TL


-- | A typescript @boolean@ represented as a Haskell 'Bool'.
tsBoolean :: TSType p 'NotObj Bool
tsBoolean = TSBaseType $ inject TSBoolean

-- | A typescript/json @number@ represented as a Haskell 'Scientific',
-- a space-efficient arbitrary-precision numeric type.
tsNumber :: TSType p 'NotObj Scientific
tsNumber = TSPrimType $ inject TSNumber

-- | A typescript/json @number@ represented as a Haskell 'Integral'
-- instance that is bounded.  Meant to represent an integer, and will fail
-- to parse on non-integers.
--
-- Use 'tsNumber' and 'invmap' for more precise control over
-- integer-vs-non-integer semantics.
tsBoundedInteger :: (Integral a, Bounded a) => TSType p 'NotObj a
tsBoundedInteger = TSPrimType $ PS TSNumber
    (\x -> case toBoundedInteger x of
            Nothing -> Left . T.pack $ "Not an integer: " <> show x
            Just i  -> Right i
    ) fromIntegral

-- | A typescript/json @number@ represented as a Haskell 'Integral'
-- instance.  Use with care, because the parser is vulnerable to
-- memory overflow-based attacks with malicious input.  Will fail to parse
-- on non-integers.
--
-- Use 'tsNumber' and 'invmap' for more precise control over
-- integer-vs-non-integer semantics.
tsInteger :: Integral a => TSType p 'NotObj a
tsInteger = TSPrimType $ PS TSNumber
    (\x -> first (\n -> T.pack $ "Not an integer: " <> show @Double n) (floatingOrInteger x))
    fromIntegral

-- | A typescript/json @number@ represented as a Haskell 'RealFloat'
-- instance.
tsRealFloat :: RealFloat a => TSType p 'NotObj a
tsRealFloat = invmap toRealFloat fromFloatDigits tsNumber

-- | A typescript/json @number@ represented as a Haskell 'Double'.
tsDouble :: TSType p 'NotObj Double
tsDouble = tsRealFloat

-- | A typescript/json @number@ represented as a Haskell 'Int'.  Will fail
-- to parse if used on a non-integer.
tsInt :: TSType p 'NotObj Int
tsInt = tsBoundedInteger

-- | A typescript/json @bigint@ represented as a Haskell 'Integer'.
tsBigInt :: TSType p 'NotObj Integer
tsBigInt = TSPrimType $ inject TSBigInt

-- | A typescript/json @string@ represented as a Haskell strict 'Text'.
tsText :: TSType p 'NotObj Text
tsText = TSPrimType $ inject TSString

-- | A typescript/json @string@ represented as a Haskell lazy 'TL.Text'.
tsLazyText :: TSType p 'NotObj TL.Text
tsLazyText = invmap TL.fromStrict TL.toStrict tsText

-- | A typescript/json @string@ represented as a Haskell 'String'.
tsString :: TSType p 'NotObj String
tsString = invmap T.unpack T.pack tsText

-- | A typescript/json string literal, represented as a Haskell '()', since
-- there is only one inhabitant.
--
-- Will only succesfully parse on the exact string.
tsStringLit :: Text -> TSType p 'NotObj ()
tsStringLit = TSBaseType . inject . TSStringLit

-- | A singleton for type-level strings, used for type-directed typescript
-- string literals.
data SSymbol s = KnownSymbol s => SSymbol

-- | A type-directed version of 'tsStringLit', where the value can be
-- generated based on type inference alone.
tsStringLitSymbol
    :: forall s p. KnownSymbol s
    => TSType p 'NotObj (SSymbol s)
tsStringLitSymbol = TSBaseType $ ICoyoneda (const ()) (const res) (TSStringLit s)
  where
    res = SSymbol
    s   = T.pack $ symbolVal res

-- | A typescript/json numeric literal, represented as a Haskell '()', since
-- there is only one inhabitant.
tsNumericLit :: Scientific -> TSType p 'NotObj ()
tsNumericLit = TSBaseType . inject . TSNumericLit

-- | A typescript/json numeric literal (restricted to an integer),
-- represented as a Haskell '()', since there is only one inhabitant.
tsIntegerLit :: Integral a => a -> TSType p 'NotObj ()
tsIntegerLit = TSBaseType . inject . TSNumericLit . fromIntegral

-- | A singleton for type-level nats, used for type-directed typescript
-- numeric literals.
data SNat n = KnownNat n => SNat

-- | A type-directed version of 'tsIntegerLit', where the value can be
-- generated based on type inference alone.
tsIntegerLitNat
    :: forall n p. KnownNat n
    => TSType p 'NotObj (SNat n)
tsIntegerLitNat = TSBaseType $ ICoyoneda (const ()) (const res) (TSNumericLit n)
  where
    res = SNat
    n   = fromIntegral $ natVal res

-- | A typescript/json numeric literal (restricted to 'Integer'),
-- represented as a Haskell '()', since there is only one inhabitant.
tsBigIntLit :: Integer -> TSType p 'NotObj ()
tsBigIntLit = TSBaseType . inject . TSBigIntLit

-- | A type-directed version of 'tsBigIntLit', where the value can be
-- generated based on type inference alone.
tsBigIntLitNat
    :: forall n p. KnownNat n
    => TSType p 'NotObj (SNat n)
tsBigIntLitNat = TSBaseType $ ICoyoneda (const ()) (const res) (TSBigIntLit n)
  where
    res = SNat
    n   = fromIntegral $ natVal res

-- | A typescript @void@ represented as a Haskell '()'.
tsVoid :: TSType p 'NotObj ()
tsVoid = TSBaseType $ inject TSVoid

-- | A typescript @undefined@ represented as a Haskell '()'.
tsUndefined :: TSType p 'NotObj ()
tsUndefined = TSBaseType $ inject TSUndefined

-- | A typescript @null@ represented as a Haskell '()'.
tsNull :: TSType p 'NotObj ()
tsNull = TSBaseType $ inject TSNull

-- | A typescript @never@ represented as a Haskell 'Void'.
tsNever :: TSType p 'NotObj Void
tsNever = TSBaseType $ inject TSNever

-- | A typescript @any@ represented and parsed as any instance of aeson's
-- 'A.FromJSON' and 'A.ToJSON'.
tsAesonAny :: (A.FromJSON a, A.ToJSON a) => TSType p 'NotObj a
tsAesonAny = tsAnyWith (unResult . A.fromJSON) A.toJSON

-- | A typescript @unknown@ represented and parsed as any instance of aeson's
-- 'A.FromJSON' and 'A.ToJSON'.
tsAesonUnknown :: (A.FromJSON a, A.ToJSON a) => TSType p 'NotObj a
tsAesonUnknown = tsUnknownWith (unResult . A.fromJSON) A.toJSON

unResult :: A.Result a -> Either Text a
unResult = \case
  A.Error   s -> Left (T.pack s)
  A.Success x -> Right x

-- | A typescript @unknown@ represented and parsed as any Haskell type,
-- using the provided parser and encoder.
tsUnknownWith
    :: (A.Value -> Either Text a)
    -> (a -> A.Value)
    -> TSType p 'NotObj a
tsUnknownWith f g = TSPrimType $ PS TSUnknown f g

-- | A typescript @any@ represented and parsed as any Haskell type,
-- using the provided parser and encoder.
tsAnyWith
    :: (A.Value -> Either Text a)
    -> (a -> A.Value)
    -> TSType p 'NotObj a
tsAnyWith f g = TSPrimType $ PS TSUnknown f g

-- | A typescript @any@ represented as aeson's 'A.Value'.  Note that
-- this must always be used in a "total" way; if you want a partial parsing
-- situation, use 'tsAnyWith'.
tsAny :: TSType p 'NotObj A.Value
tsAny = tsAnyWith Right id

-- | A typescript @unknown@ represented as aeson's 'A.Value'.  Note that
-- this must always be used in a "total" way; if you want a partial parsing
-- situation, use 'tsUnknownWith'.
tsUnknown :: TSType p 'NotObj A.Value
tsUnknown = tsAnyWith Right id

