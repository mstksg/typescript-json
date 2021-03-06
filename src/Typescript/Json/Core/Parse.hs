{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Typescript.Json.Core.Parse (
    parseType
  , showParseErr
  , ParseErr(..)
  ) where

import           Control.Monad.Trans.State
import           Data.Foldable
import           Data.Functor.Apply
import           Data.Functor.Combinator hiding    (Comp(..))
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.Functor.Invariant.DecAlt
import           Data.Some                         (Some(..))
import           Data.Type.Nat
import           Typescript.Json.Core.Print
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators
import qualified Data.Aeson.BetterErrors           as ABE
import qualified Data.Vec.Lazy                     as Vec
import qualified Data.Vector                       as V

showParseErr :: ParseErr -> String
showParseErr = show -- TODO

parseEnumLit :: EnumLit -> ABE.Parse () ()
parseEnumLit = \case
    ELString t -> ABE.withText $ eqOrFail (const ()) t
    ELNumber t -> ABE.withScientific $ eqOrFail (const ()) t

eqOrFail :: Eq a => (a -> e) -> a -> a -> Either e ()
eqOrFail e x y
  | x == y    = Right ()
  | otherwise = Left (e y)

parsePrim :: TSPrim a -> ABE.Parse ParseErr a
parsePrim = \case
    TSNumber    -> ABE.asScientific
    TSBigInt    -> ABE.asIntegral
    TSString    -> ABE.asText
    TSUnknown -> ABE.asValue
    TSAny -> ABE.asValue

parseBase :: TSBase a -> ABE.Parse ParseErr a
parseBase = \case
    TSBoolean   -> ABE.asBool
    TSStringLit t -> ABE.withText $ eqOrFail (PEInvalidString t) t
    TSNumericLit t -> ABE.withScientific $ eqOrFail (PEInvalidNumber t) t
    TSBigIntLit t -> ABE.withIntegral $ eqOrFail (PEInvalidBigInt t) t
    TSVoid -> ABE.asNull
    TSUndefined -> ABE.asNull
    TSNull -> ABE.asNull
    TSNever -> ABE.throwCustomError PENever


parseNamedPrim :: TSNamedBase a -> ABE.Parse ParseErr a
parseNamedPrim = \case
    TSEnum es -> ABE.mapError (\_ -> PEInvalidEnum (toList es)) $ Vec.ifoldr
      (\i (_, e) ps -> (i <$ parseEnumLit e) ABE.<|> ps)
      (ABE.throwCustomError ())
      es

type Parse = ABE.ParseT ParseErr Identity

parseType
    :: forall k a. ()
    => TSType 'Z k a
    -> Parse a
parseType = \case
    TSArray ts -> unwrapFunctor $ interpretILan (WrapFunctor . ABE.eachInArray . parseType) ts
    TSTuple ts -> do
      (res, n) <- flip runStateT 0 $ (`interpret` ts) $ \t -> StateT $ \i ->
        (,i+1) <$> ABE.nth i (withTSType_ parseType t)
      ABE.withArray $ \xs ->
        if V.length xs > n
          then Left $ PEExtraTuple n (V.length xs)
          else pure res
    TSObject ts -> parseKeyVal ts
    TSSingle ts -> parseType ts
    TSUnion ts ->
      let us = icollect1 (withTSType_ ppType) $ decAltNonEmptyF_ ts
      in  foldr (ABE.<|>) (ABE.throwCustomError (PENotInUnion us)) $
            runNonEmptyF . decAltNonEmptyF $ hmap (withTSType_ parseType) ts
    TSNamedType (TSNamed _ nt :$ xs) -> case nt of
      TSNFunc t -> parseType (tsApply t xs)
      TSNBaseType t -> interpret parseNamedPrim (icoToCoco t)
    TSIntersection ts -> unwrapApplicative $ interpret (WrapApplicative . parseType) ts
    TSTransformType tf -> interpret (parseType . applyTransform) (icoToCoco tf)
    TSPrimType PS{..} -> either (ABE.throwCustomError . PEPrimitive (Some psItem)) pure . psParser
                     =<< parsePrim psItem
    TSBaseType (ICoyoneda _ g x) -> g <$> parseBase x
  where
    parseKeyVal :: TSKeyVal 'Z ~> Parse
    parseKeyVal = interpret
        ( unwrapFunctor . interpretObjMember
            (\_ k -> WrapFunctor . ABE.key    k . withTSType_ parseType)
            (\_ k -> WrapFunctor . ABE.keyMay k . withTSType_ parseType)
        )

