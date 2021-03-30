{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE EmptyCase       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators   #-}

module Typescript.Json.Core.Encode (
  -- * to value
    enumLitToValue
  , primToValue
  , typeToValue
  , encodeEnumLit
  , primToEncoding
  , typeToEncoding
  ) where

import           Data.Functor.Combinator hiding    (Comp(..))
import           Data.Functor.Contravariant
import           Data.Functor.Invariant.DecAlt
import           Data.HFunctor.Route
import           Data.Type.Nat
import           Data.Void
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators
import qualified Data.Aeson                        as A
import qualified Data.Aeson.Encoding               as AE
import qualified Data.Aeson.Types                  as A
import qualified Data.Vec.Lazy                     as Vec
import qualified Data.Vector                       as V



encodeEnumLit :: EnumLit -> A.Encoding
encodeEnumLit = \case
    ELString t -> AE.text t
    ELNumber n -> AE.scientific n

primToEncoding :: TSPrim a -> a -> A.Encoding
primToEncoding = \case
    TSBoolean -> AE.bool
    TSNumber  -> AE.scientific
    -- hm...
    TSBigInt  -> AE.integer
    TSString  -> AE.text
    TSStringLit t -> \_ -> AE.text t
    TSNumericLit n -> \_ -> AE.scientific n
    -- hm...
    TSBigIntLit n -> \_ -> AE.integer n
    TSUnknown -> AE.value
    TSAny -> AE.value

baseToEncoding :: TSBase a -> a -> A.Encoding
baseToEncoding = \case
    -- hm...
    TSVoid -> \_ -> AE.null_
    TSUndefined -> \_ -> AE.null_
    TSNull -> \_ -> AE.null_
    TSNever -> absurd

namedPrimToEncoding :: TSNamedPrim a -> a -> A.Encoding
namedPrimToEncoding = \case
    TSEnum e -> \i -> encodeEnumLit (snd (e Vec.! i))

objTypeToEncoding :: TSType 'Z 'IsObj a -> Op A.Series a
objTypeToEncoding = \case
    TSObject       ts -> keyValToValue ts
    TSIntersection ts -> preDivisibleT objTypeToEncoding ts
    TSNamedType (TSNamed _ nt :$ xs) -> case nt of
      TSNFunc f -> objTypeToEncoding (tsApply f xs)
    TSTransformType tf -> interpret (objTypeToEncoding . applyTransform) $ icoToContraco tf
  where
    keyValToValue :: TSKeyVal 'Z ~> Op A.Series
    keyValToValue = preDivisibleT
        ( interpretObjMember
            (\_ k t -> Op           $ \x -> k A..= withTSType_ typeToValue t x)
            (\_ k t -> Op . foldMap $ \x -> k A..= withTSType_ typeToValue t x)
        )

typeToEncoding :: TSType 'Z k a -> a -> A.Encoding
typeToEncoding = \case
    TSArray ts        -> AE.list id
                       . getOp (interpretILan (\t -> Op ( map (typeToEncoding t))) ts)
    TSTuple ts        -> AE.list id
                       . getOp (preDivisibleT (\t -> Op $ \x -> [withTSType_ typeToEncoding t x]) ts)
    TSObject    ts    -> A.pairs . getOp (objTypeToEncoding (TSObject ts))
    TSSingle ts       -> typeToEncoding ts
    TSUnion ts        -> getOp $ runContraDecAlt1 (Op . withTSType_ typeToEncoding) ts
    TSNamedType (TSNamed _ nt :$ xs) -> case nt of
      TSNFunc f -> typeToEncoding (tsApply f xs)
      TSNPrimType PS{..} -> namedPrimToEncoding psItem . psSerializer
    TSIntersection ts -> A.pairs . getOp (objTypeToEncoding (TSIntersection ts))
    TSTransformType tf -> typeToEncoding (interpret applyTransform tf)
    TSPrimType PS{..} -> primToEncoding psItem . psSerializer
    TSBaseType (ICoyoneda f _ x) -> baseToEncoding x . f

enumLitToValue :: EnumLit -> A.Value
enumLitToValue = \case
    ELString t -> A.String t
    ELNumber n -> A.Number n

primToValue :: TSPrim a -> a -> A.Value
primToValue = \case
    TSBoolean -> A.Bool
    TSNumber  -> A.Number
    -- hm...
    TSBigInt  -> A.Number . fromIntegral
    TSString  -> A.String
    TSStringLit t -> \_ -> A.String t
    TSNumericLit n -> \_ -> A.Number n
    -- hm...
    TSBigIntLit n -> \_ -> A.Number (fromIntegral n)
    TSUnknown -> id
    TSAny -> id

baseToValue :: TSBase a -> a -> A.Value
baseToValue = \case
    -- hm...
    TSVoid -> \_ -> A.Null
    TSUndefined -> \_ -> A.Null
    TSNull -> \_ -> A.Null
    TSNever -> absurd

namedPrimToValue :: TSNamedPrim a -> a -> A.Value
namedPrimToValue = \case
    TSEnum e -> \i -> enumLitToValue (snd (e Vec.! i))

objTypeToValue :: TSType 'Z 'IsObj a -> Op [A.Pair] a
objTypeToValue = \case
    TSObject       ts -> keyValToValue ts
    TSIntersection ts -> preDivisibleT objTypeToValue ts
    TSNamedType (TSNamed _ nt :$ xs) -> case nt of
      TSNFunc f -> objTypeToValue (tsApply f xs)
    TSTransformType tf -> objTypeToValue (interpret applyTransform tf)
  where
    keyValToValue :: TSKeyVal 'Z ~> Op [A.Pair]
    keyValToValue = preDivisibleT
        ( interpretObjMember
            (\_ k t -> Op           $ \x -> [k A..= withTSType_ typeToValue t x])
            (\_ k t -> Op . foldMap $ \x -> [k A..= withTSType_ typeToValue t x])
        )

typeToValue
    :: TSType 'Z k a -> a -> A.Value
typeToValue = \case
    TSArray ts        -> A.Array
                       . V.fromList
                       . getOp (interpretILan (\t -> Op ( map (typeToValue t))) ts)
    TSTuple ts        -> A.Array
                       . V.fromList
                       . getOp (preDivisibleT (\t -> Op $ \x -> [withTSType_ typeToValue t x]) ts)
    TSObject    ts    -> A.object . getOp (objTypeToValue (TSObject ts))
    TSSingle ts       -> typeToValue ts
    TSUnion ts        ->  getOp $ runContraDecAlt1 (Op . withTSType_ typeToValue) ts
    TSNamedType (TSNamed _ nt :$ xs) -> case nt of
      TSNFunc f -> typeToValue (tsApply f xs)
      TSNPrimType PS{..} -> namedPrimToValue psItem . psSerializer
    TSIntersection ts -> A.object . getOp (objTypeToValue (TSIntersection ts))
    TSTransformType tf -> typeToValue (interpret applyTransform tf)
    TSPrimType PS{..} -> primToValue psItem . psSerializer
    TSBaseType (ICoyoneda f _ x) -> baseToValue x . f

