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
    -- TSPrim(..)
  -- , TSNamedPrim(..)
  -- , EnumLit(..)
  -- , TSType(..)
  -- , TSType_(..)
  -- , TSNamed(..)
  -- , TSNamed_(..)
  -- , withTSNamed_
  -- , TSNameable(..)
  -- , ObjMember(..)
  -- , TSKeyVal
  -- , onTSType_
  -- , decideTSType_
  -- , mapTSType_
  -- , withTSType_
  -- , IsObjType(..)
  -- , SIsObjType(..)
  -- , tsObjType
  -- , tsShift
  -- , SNat_(..)
  -- -- * Generics
  -- , TSTypeF(..)
  -- , TSTypeF_(..)
  -- , TSApplied(..)
  -- , TSAppliedF(..)
  -- , mapTSTypeF_
  -- , withTSTypeF_
  -- , tsApply
  -- , tsApply1
  -- , tsApplyVar
  -- * utility func
  -- , interpretObjMember
  -- , reAssign
  -- , isAssignable
  -- , eqTSPrim
  ) where

-- import           Control.Applicative
-- import           Control.Applicative.Free
-- import           Control.Monad
-- import           Control.Monad.Trans.State
-- import           Data.Bifunctor
-- import           Data.Fin                                  (Fin(..))
-- import           Data.Foldable
-- import           Data.Functor
-- import           Data.Functor.Apply
-- import           Data.Functor.Apply.Free
-- import           Data.Functor.Combinator hiding            (Comp(..))
-- import           Data.Functor.Compose
-- import           Data.Functor.Contravariant
-- import           Data.Functor.Contravariant.Divisible.Free (Dec1(..))
-- import           Data.Functor.Identity
-- import           Data.Functor.Invariant
-- import           Data.GADT.Show
-- import           Data.HFunctor.Route
-- import           Data.Kind
-- import           Data.Map                                  (Map)
-- import           Data.Maybe
-- import           Data.Ord
-- import           Data.Profunctor
-- import           Data.Proxy
-- import           Data.SOP                                  (NP(..), K(..))
-- import           Data.Scientific                           (Scientific, toBoundedInteger)
-- import           Data.Semigroup                            (First(..))
-- import           Data.Set                                  (Set)
-- import           Data.Some                                 (Some(..))
-- import           Data.Text                                 (Text)
-- import           Data.Type.Equality
-- import           Data.Type.Nat
-- import           Data.Vec.Lazy                             (Vec(..))
-- import           Data.Void
-- import           Typescript.Json.Core.Encode
-- import           Typescript.Json.Core.Parse
-- import           Typescript.Json.Types
-- import           Typescript.Json.Types.Combinators
-- import           Typescript.Json.Types.SNat
-- import qualified Control.Applicative.Lift                  as Lift
-- import qualified Data.Aeson                                as A
-- import qualified Data.Aeson.BetterErrors                   as ABE
-- import qualified Data.Aeson.Encoding                       as AE
-- import qualified Data.Aeson.Types                          as A
-- import qualified Data.Fin                                  as Fin
-- import qualified Data.Functor.Combinator.Unsafe            as FCU
-- import qualified Data.Graph.Inductive.Graph                as FGL
-- import qualified Data.Graph.Inductive.PatriciaTree         as FGL
-- import qualified Data.Graph.Inductive.Query.DFS            as FGL
-- import qualified Data.Map                                  as M
-- import qualified Data.SOP                                  as SOP
-- import qualified Data.Set                                  as S
-- import qualified Data.Text                                 as T
-- import qualified Data.Type.Nat                             as Nat
-- import qualified Data.Vec.Lazy                             as Vec
-- import qualified Data.Vector                               as V
-- import qualified Prettyprinter                             as PP


