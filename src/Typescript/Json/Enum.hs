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

module Typescript.Json.Enum (
  -- * With Vector
    FinIso(..), tsEnumWith, tsIntEnumFrom, tsIntEnum
  -- * With Map
  , EnumMap(..), tsEnumMap
  -- * With Enum
  , tsFinEnum, tsFinIntEnum
  ) where

import           Control.Monad.Trans.State
import           Data.Fin hiding                      (absurd)
import           Data.Foldable
import           Data.Functor.Combinator
import           Data.Functor.Invariant
import           Data.Map                             (Map)
import           Data.Text                            (Text)
import           Data.Traversable
import           Data.Vec.Lazy                        (Vec)
import           Typescript.Json.Types
import qualified Data.Fin.Enum                        as FE
import qualified Data.Map                             as M
import qualified Data.Vec.Lazy                        as Vec


data EnumMap a = EnumMap
    { emGet :: Map EnumLit (Text, a)
    , emPut :: a -> EnumLit
    }
-- the main issue is neeing to not require a to be Eq or anything and so
-- not requiring a lookup. the partial part is making sure every enumlit is
-- in the map

runEnumMap :: EnumMap a -> (forall n. FinIso n a -> Vec n (Text, EnumLit) -> r) -> r
runEnumMap EnumMap{..} f = Vec.reifyList (M.toList emGet) $ \(xs :: Vec n (EnumLit, (Text, a))) ->
    let res :: Vec n (Text, EnumLit)
        res = fmap (\(l,(c,_)) -> (c, l)) xs
        outVec = snd . snd <$> xs
        xsMap :: Map EnumLit (Fin n)
        xsMap = M.fromList . toList $ Vec.imap (\i (l, _) -> (l, i)) xs
        lu k = case M.lookup (emPut k) xsMap of
          Nothing -> error $ "Bad EnumMap given when using tsEnumMap: Map missing key " <> show (emPut k)
          Just x  -> x
        fi = FinIso
          { fiGet = (outVec Vec.!)
          , fiPut = lu
          }
    in  f fi res

tsEnumMap :: Text -> EnumMap a -> TSNamed p 'NotObj '[] '[] a
tsEnumMap nm em = runEnumMap em (tsEnumWith nm)

tsFinEnum
    :: FE.Enum a
    => Text
    -> Vec (FE.EnumSize a) (Text, EnumLit)
    -> TSNamed p 'NotObj '[] '[] a
tsFinEnum nm = tsEnumWith nm $ FinIso
    { fiGet = FE.to
    , fiPut = FE.from
    }

tsFinIntEnum
    :: FE.Enum a
    => Text
    -> Vec (FE.EnumSize a) Text
    -> TSNamed p 'NotObj '[] '[] a
tsFinIntEnum nm = tsIntEnum nm $ FinIso
    { fiGet = FE.to
    , fiPut = FE.from
    }


data FinIso n a = FinIso
    { fiGet :: Fin n -> a
    , fiPut :: a -> Fin n
    }

instance Invariant (FinIso n) where
    invmap f g (FinIso x y) = FinIso (f . x) (y . g)

tsEnumWith
    :: Text
    -> FinIso n a
    -> Vec n (Text, EnumLit)
    -> TSNamed p 'NotObj '[] '[] a
tsEnumWith nm FinIso{..} xs = TSNamed
    { tsnName = nm
    , tsnType = TSNBaseType $
        invmap fiGet fiPut $ inject (TSEnum xs)
    }

tsIntEnum
    :: Text
    -> FinIso n a
    -> Vec n Text
    -> TSNamed p 'NotObj '[] '[] a
tsIntEnum nm = tsIntEnumFrom nm 0

tsIntEnumFrom
    :: Text
    -> Int
    -> FinIso n a
    -> Vec n Text
    -> TSNamed p 'NotObj '[] '[] a
tsIntEnumFrom nm i0 fi xs = tsEnumWith nm fi xs'
  where
    xs' = flip evalState i0 . for xs $ \x -> state $ \i ->
      ((x, ELNumber (fromIntegral i)), i+1)


