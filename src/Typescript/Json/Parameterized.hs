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

module Typescript.Json.Parameterized (
  -- * Generics
    tsGeneric
  , tsGeneric1
  , tsGeneric2
  , tsGeneric3
  , tsGenericInterface
  , tsApplied1
  , tsApplied2
  , tsApplied3
  , tsApplied
  , tsApply1
  , tsApply2
  , tsApply3
  , tsApply
  ) where

import           Data.Functor.Combinator
import           Data.Text                         (Text)
import           Data.Type.Nat                     (Plus)
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators

-- | Create a single-argument generic (parameterized) type.
--
-- For example, we could make a type imitating 'Maybe' in Haskell:
--
-- @
-- mkMaybe :: TSType_ p a -> TSType_ p (Maybe a)
-- mkMaybe = tsUnion $ decide (maybe (Left ()) Right) $
--     (tsTagged
-- @
tsGeneric1
    :: Text                     -- ^ Name of the type
    -> Param p a e              -- ^ Name of the parameter (used for printing) and what it extends
    -> (forall r. SNat_ r -> Arg_ (Plus r p) a e -> TSType (Plus r p) k b)         -- ^ Make a type, given the type parameter
    -> TSNamed p k '[a] '[e] b
tsGeneric1 n p f = tsGeneric n (p :** Nil2) $ \rs (t :** Nil2) -> f rs t

tsGeneric2
    :: Text
    -> Param p a ea
    -> Param p b eb
    -> (forall r. SNat_ r -> Arg_ (Plus r p) a ea -> Arg_ (Plus r p) b eb -> TSType (Plus r p) k c)
    -> TSNamed p k '[a, b] '[ea, eb] c
tsGeneric2 n p q f = tsGeneric n (p :** q :** Nil2) $
            \rs (t :** u :** Nil2) -> f rs t u

tsGeneric3
    :: Text
    -> Param p a ea
    -> Param p b eb
    -> Param p c ec
    -> (forall r. SNat_ r -> Arg_ (Plus r p) a ea -> Arg_ (Plus r p) b eb -> Arg_ (Plus r p) c ec -> TSType (Plus r p) k d)
    -> TSNamed p k '[a, b, c] '[ea, eb, ec] d
tsGeneric3 n p q r f = tsGeneric n (p :** q :** r :** Nil2) $
            \rs (t :** u :** v :** Nil2) -> f rs t u v

-- | A parameterized type with multiple parameters.
tsGeneric
    :: Text                 -- ^ Name
    -> NP2 (Param p) as es       -- ^ Name of parameters and extends
    -> (forall r. SNat_ r -> NP2 (Arg_ (Plus r p)) as es -> TSType (Plus r p) k b)   -- ^ Type function
    -> TSNamed p k as es b
tsGeneric n ps f = TSNamed
    { tsnName = n
    , tsnType = TSNFunc $ TSGeneric ps f
    }

tsGenericInterface
    :: Text             -- ^ name
    -> NP2 (Param p) as es       -- ^ Name of parameters and extends
    -> Lift (TSAppliedF p 'IsObj as es) a   -- ^ if it extends any other object
    -> (forall r. SNat_ r -> NP2 (Arg_ (Plus r p)) as es -> TSKeyVal (Plus r p) b)  -- how to use type variables
    -> TSNamed p 'IsObj as es (a, b)
tsGenericInterface n ps e f = TSNamed
    { tsnName = n
    , tsnType = TSNFunc $ TSGenericInterface ps (,) id e f
    }

tsApplied
    :: TSNamed p k as es b
    -> NP2 (Arg_ p) as es
    -> TSType p k b
tsApplied f x = TSNamedType (f :$ x)

tsApply2
    :: TSTypeF p k '[a,b] '[ea,eb] c      -- ^ type function
    -> Arg_ p a ea         -- ^ thing to apply
    -> Arg_ p b eb         -- ^ thing to apply
    -> TSType p k c
tsApply2 f t u = tsApply f (t :** u :** Nil2)

tsApply3
    :: TSTypeF p k '[a,b,c] '[ea,eb,ec] d      -- ^ type function
    -> Arg_ p a ea         -- ^ thing to apply
    -> Arg_ p b eb         -- ^ thing to apply
    -> Arg_ p c ec         -- ^ thing to apply
    -> TSType p k d
tsApply3 f t u v = tsApply f (t :** u :** v :** Nil2)

tsApplied1
    :: TSNamed p k '[a] '[e] b
    -> Arg_ p a e
    -> TSType p k b
tsApplied1 tf tx = tsApplied tf (tx :** Nil2)

tsApplied2
    :: TSNamed p k '[a, b] '[ea, eb] c
    -> Arg_ p a ea
    -> Arg_ p b eb
    -> TSType p k c
tsApplied2 tf tx ty = tsApplied tf (tx :** ty :** Nil2)

tsApplied3
    :: TSNamed p k '[a, b, c] '[ea, eb, ec] d
    -> Arg_ p a ea
    -> Arg_ p b eb
    -> Arg_ p c ec
    -> TSType p k d
tsApplied3 tf tx ty tz = tsApplied tf (tx :** ty :** tz :** Nil2)

