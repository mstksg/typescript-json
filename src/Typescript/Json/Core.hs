{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedLabels           #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

module Typescript.Json.Core (
    mkArg, mkArgs
  , unsafeMkArg, unsafeMkArgs
  ) where

import           Data.Functor.Combinator hiding    (Comp(..))
import           Data.Kind
import           Data.SOP                          (NP(..))
import           Data.Type.Nat
import           Typescript.Json.Core.Assign
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators

mkArg :: Param 'Z a e -> TSType 'Z k a -> Maybe (Arg_ 'Z a e)
mkArg Param{..} t = Arg_ . Arg t <$> htraverse (withTSType_ (reAssign t)) paramExtends

mkArgs :: NP2 (Param 'Z) as es -> NP (TSType_ 'Z) as -> Maybe (NP2 (Arg_ 'Z) as es)
mkArgs = \case
    Nil2 -> \case
      Nil -> Just Nil2
    p :** ps -> \case
      TSType_ x :* xs -> (:**) <$> mkArg p x <*> mkArgs ps xs

unsafeMkArg :: Param 'Z a e -> TSType 'Z k a -> Arg_ 'Z a e
unsafeMkArg Param{..} t = Arg_ . Arg t $ hmap (withTSType_ (unsafeReAssign t)) paramExtends

unsafeMkArgs :: NP2 (Param 'Z) as es -> NP (TSType_ 'Z) as -> NP2 (Arg_ 'Z) as es
unsafeMkArgs = \case
    Nil2 -> \case
      Nil -> Nil2
    p :** ps -> \case
      TSType_ x :* xs -> unsafeMkArg p x :** unsafeMkArgs ps xs

safeMkArg :: Param 'Z a 'Nothing -> TSType 'Z k a -> Arg_ 'Z a 'Nothing
safeMkArg Param{..} t = Arg_ $ Arg t MPNothing

class SafeMkArgs (as :: [Type]) (es :: [Maybe Type]) where
    safeMkArgs :: NP2 (Param 'Z) as es -> NP (TSType_ 'Z) as -> NP2 (Arg_ 'Z) as es

instance SafeMkArgs '[] '[] where
    safeMkArgs _ _ = Nil2

instance SafeMkArgs as es => SafeMkArgs (a ': as) ('Nothing ': es) where
    safeMkArgs = \case
      p :** ps -> \case
        TSType_ t :* ts -> safeMkArg p t :** safeMkArgs ps ts
