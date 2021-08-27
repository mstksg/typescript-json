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
  , module Typescript.Json.Primitive
  , module Typescript.Json.Collection
  , module Typescript.Json.Union
  , module Typescript.Json.Enum
  , module Typescript.Json.Parameterized
  -- ** Named
  , tsNamed, tsNamed_
  -- * Printing
  , ppType
  , ppType_
  , ppNamed
  , ppNamed_
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

import           Data.Text                         (Text)
import           Typescript.Json.Collection
import           Typescript.Json.Core.Encode
import           Typescript.Json.Core.Parse
import           Typescript.Json.Core.Print
import           Typescript.Json.Enum
import           Typescript.Json.Parameterized
import           Typescript.Json.Primitive
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators
import           Typescript.Json.Union
import qualified Data.Aeson.BetterErrors           as ABE
import qualified Data.Aeson.Encoding               as AE
import qualified Data.ByteString                   as BS
import qualified Data.ByteString.Lazy              as BSL
import qualified Data.Type.Nat                     as Nat

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

