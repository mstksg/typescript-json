{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}

module Typescript.Json.Core.Assign (
    isAssignable
  , reAssign
  , unsafeReAssign
  , unsafeAssign
  -- , isNullable
  ) where

import           Control.Applicative.Free
import           Control.Monad
import           Data.Bifunctor
import           Data.Coerce
import           Data.Functor
import           Data.Functor.Apply
import           Data.Functor.Combinator hiding    (Comp(..))
import           Data.Functor.Compose
import           Data.Functor.Contravariant
import           Data.Functor.Invariant
import           Data.HFunctor.Route
import           Data.Map                          (Map)
import           Data.Maybe
import           Data.Profunctor
import           Data.Semigroup                    (First(..))
import           Data.Some                         (Some(..))
import           Data.Text                         (Text)
import           Data.Type.Equality
import           Data.Type.Nat
import           Data.Vec.Lazy                     (Vec(..))
import           Data.Void
import           Typescript.Json.Core.Encode
import           Typescript.Json.Core.Parse
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators
import           Typescript.Json.Types.SNat
import qualified Data.Aeson                        as A
import qualified Data.Aeson.BetterErrors           as ABE
import qualified Data.Fin                          as Fin
import qualified Data.Map                          as M
import qualified Data.Text                         as T
import qualified Data.Vec.Lazy                     as Vec

-- | Internal newtype wrapper with the appropriate instances, so we don't
-- need to leak the instances
newtype WrappedAssign a b = WrapAssign { unwrapAssign :: Assign a b }

deriving via (Star (Either Text)) instance Profunctor WrappedAssign
deriving via (Star (Either Text) a) instance Functor (WrappedAssign a)
deriving via (Star (Either Text) a) instance Applicative (WrappedAssign a)
deriving via (WrappedApplicative (WrappedAssign a)) instance Apply (WrappedAssign a)

pureA :: a -> Assign r a
pureA = unwrapAssign . pure


-- | answers: is X assignable to Y?
--
-- https://basarat.gitbook.io/typescript/type-system/type-compatibility
isAssignable :: TSType 'Z k a -> TSType 'Z j b -> Bool
isAssignable t u = isJust $ reAssign t u

unsafeReAssign :: TSType 'Z k a -> TSType 'Z j b -> Assign a b
unsafeReAssign x = fromMaybe badAssign . reAssign x
  where
    badAssign = Assign $ \_ -> Left "unsafeReAssign: Unsafe assignment failure"

-- | Completely 100% unsafe, but at least it doesn't require having a type
-- without any free variables
unsafeAssign :: Assign a b
unsafeAssign = Assign $ \_ -> Left "unsafeAssign: Unsafe meaningless assignment"

-- isNullable :: TSType 'Z k a -> Maybe (Assign () a)
-- isNullable = reAssign $ TSPrimType (inject TSNull)

-- | a can be assigned as a b.  the function will "lose" information.
--
-- assumes --stictNullChecks
-- https://www.typescriptlang.org/docs/handbook/type-compatibility.html#advanced-topics
reAssignPrim :: (r -> a) -> TSPrim a -> TSType 'Z k b -> Maybe (Assign r b)
reAssignPrim z = \case
    TSBoolean -> \case
      TSPrimType (PS TSBoolean f _) -> Just . Assign $ f . z
      _ -> Nothing
    TSNumber -> \case
      TSPrimType (PS TSNumber f _) -> Just . Assign $ f . z
      -- compatible with num as long as there is at least one number, or is
      -- empty.  this is different than the spec but w/e
      TSNamedType (TSNamed{..} :$ _) -> case tsnType of
        TSNPrimType (PS (TSEnum cs) f _)
          | null cs   -> Just . Assign $ \_ -> Left $ "Number out of range for empty Enum"
          | otherwise -> do
              let numberOpts =
                    [ (i, n)
                    | (i, (_, ELNumber n)) <- Vec.toList $ Vec.imap (,) cs
                    ]
              guard $ not (null numberOpts)
              pure . Assign $ \(z->m) ->
                case getFirst <$> foldMap (\(i, n) -> First i <$ guard (n == m)) numberOpts of
                  Nothing -> Left $ "Number " <> T.pack (show m) <> " out of range for Enum: " <> T.pack (show cs)
                  Just x  -> f x
        TSNFunc _ -> Nothing
      _ -> Nothing
    TSBigInt -> \case
      TSPrimType (PS TSBigInt f _) -> Just . Assign $ f . z
      _ -> Nothing
    TSString -> \case
      TSPrimType (PS TSString f _) -> Just . Assign $ f . z
      _ -> Nothing
    -- hey these have to be assignable to strings
    TSStringLit s -> \case
      TSPrimType (PS (TSStringLit t) f _) -> Assign (f . z) <$ guard (s == t)
      TSPrimType (PS TSString f _) -> Just . Assign $ \_ -> f s
      _ -> Nothing
    TSNumericLit s -> \case
      TSPrimType (PS (TSNumericLit t) f _) -> Assign (f . z) <$ guard (s == t)
      TSPrimType (PS TSNumber f _) -> Just . Assign $ \_ -> f s
      _ -> Nothing
    TSBigIntLit s -> \case
      TSPrimType (PS (TSBigIntLit t) f _) -> Assign (f . z) <$ guard (s == t)
      TSPrimType (PS TSBigInt f _) -> Just . Assign $ \_ -> f s
      _ -> Nothing
    TSUnknown -> \case
      TSPrimType (PS TSUnknown f _) -> Just . Assign $ f . z
      _ -> Nothing
    TSAny -> \case
      TSPrimType (PS TSNever _ _) -> Nothing
      t -> Just . Assign $ first (T.unlines . ABE.displayError (T.pack . showParseErr)) . ABE.parseValue (parseType t) . z
    TSVoid -> \case
      TSPrimType (PS TSAny f _) -> Just . Assign $ \_ -> f A.Null
      TSPrimType (PS TSUnknown f _) -> Just . Assign $ \_ -> f A.Null
      TSPrimType (PS TSVoid f _) -> Just . Assign $ f . z
      _ -> Nothing
    TSUndefined -> \case
      TSPrimType (PS TSAny f _) -> Just . Assign $ \_ -> f A.Null
      TSPrimType (PS TSUnknown f _) -> Just . Assign $ \_ -> f A.Null
      TSPrimType (PS TSVoid f _) -> Just . Assign $ f . z
      TSPrimType (PS TSUndefined f _) -> Just . Assign $ f . z
      _ -> Nothing
    TSNull -> \case
      TSPrimType (PS TSAny f _) -> Just . Assign $ \_ -> f A.Null
      TSPrimType (PS TSUnknown f _) -> Just . Assign $ \_ -> f A.Null
      TSPrimType (PS TSNull f _) -> Just . Assign $ f . z
      _ -> Nothing
    -- never can be anything
    TSNever -> \_ -> Just . Assign $ Right . absurd . z


-- | If X is assignable to Y, then convert x to the more general y,
-- potentially losing information.
reAssign :: TSType 'Z k a -> TSType 'Z j b -> Maybe (Assign a b)
reAssign t0 = case t0 of
    TSArray (ILan _ g t) -> loopReAssign t0 $ \case
      TSArray (ILan f' _ u) ->
        Assign . dimap g (fmap f' . sequence) . map . runAssign <$> reAssign t u
      _ -> Nothing
    TSTuple (PreT xs) -> loopReAssign t0 $ \case
      TSTuple (PreT ys) -> reAssignTuple xs ys
      _ -> Nothing
    TSObject xs -> reAssignIsObj (TSObject xs)
    TSSingle x -> loopReAssign t0 (reAssign x)
    TSUnion (PostT xs) -> \y -> fmap (Assign . getOp) . getCompose $
      interpret (withTSType_ (Compose . fmap (Op . runAssign) . (`reAssign` y)) . getPost) xs
    TSIntersection xs -> reAssignIsObj (TSIntersection xs)
    TSNamedType (TSNamed{..} :$ ps) -> case tsnType of
      TSNFunc tf -> reAssign (tsApply tf ps)
      TSNPrimType (PS{..}) -> case psItem of
        TSEnum cs -> loopReAssign t0 $ \case
          -- compatible with num as long as there is at least one number, or is
          -- empty.  this is different than the spec but w/e
          TSPrimType (PS TSNumber f _) -> case cs of
            VNil -> Just . Assign $ \i -> Right $ Fin.absurd (psSerializer i)
            _ ->
              let numberOpts =
                    [ (i, n)
                    | (i, (_, ELNumber n)) <- Vec.toList $ Vec.imap (,) cs
                    ]
              in  guard (not (null numberOpts)) $> Assign (\i ->
                     case snd $ cs Vec.! psSerializer i of
                       ELNumber n -> f n
                       ELString s -> Left $ "Enum mismatch: expected number, got " <> s
                  )
          TSNamedType (TSNamed nm nt :$ _) -> case nt of
            TSNPrimType (PS (TSEnum ds) f _) -> do
              guard $ tsnName == nm
              Refl <- vecSame (snd <$> cs) (snd <$> ds)
              guard $ cs == ds
              pure . Assign $ f . psSerializer
            TSNFunc _ -> Nothing
          _ -> Nothing
    TSPrimType (PS xi _ xs) -> loopReAssign t0 $ reAssignPrim xs xi

-- | Loops on being TSNullable or TSSingle or TSNamedType TSNFunc.  Also
-- cuts things off for 'Any'/'Unknown'
loopReAssign
    :: forall a b k l. ()
    => TSType 'Z l a
    -> (forall j c. TSType 'Z j c -> Maybe (Assign a c))
    -> TSType 'Z k b
    -> Maybe (Assign a b)
loopReAssign z f = go
  where
    go :: TSType 'Z j c -> Maybe (Assign a c)
    go = \case
      TSSingle t -> go t
      TSNamedType (TSNamed _ (TSNFunc tf) :$ ps) -> go (tsApply tf ps)
      TSUnion ts -> fmap unwrapAssign . getCompose $ postAltT (Compose . fmap WrapAssign . withTSType_ go) ts
      TSPrimType (PS TSAny g _) -> Just . Assign $ g . typeToValue z
      TSPrimType (PS TSUnknown g _) -> Just . Assign $ g . typeToValue z
      t -> f t

reAssignTuple
    :: Ap (Pre a (TSType_ 'Z)) c
    -> Ap (Pre b (TSType_ 'Z)) d
    -> Maybe (Assign a d)
reAssignTuple = \case
    Pure _ -> \case
      Pure y -> Just $ pureA y
      Ap _ _ -> Nothing
    Ap (f :>$<: TSType_ x) xs -> \case
      Pure _ -> Nothing
      Ap (_ :>$<: TSType_ y) ys -> do
        rxs <- reAssign x y
        rys <- reAssignTuple xs ys
        Just . unwrapAssign $ WrapAssign rys <*> lmap f (WrapAssign rxs)

-- TODO: can we loopReAssign everything?
reAssignIsObj :: TSType 'Z 'IsObj a -> TSType 'Z k b -> Maybe (Assign a b)
reAssignIsObj x = \case
    TSArray _  -> Nothing
    TSTuple _ -> Nothing
    TSSingle y -> reAssignIsObj x y
    TSObject y -> assembleIsObj mp (TSObject y)
    TSUnion  _ -> undefined -- TODO: do the whole thing
    TSNamedType (TSNamed{..} :$ ps) -> case tsnType of
      TSNFunc tf -> reAssignIsObj x (tsApply tf ps)
      TSNPrimType _ -> Nothing
    TSIntersection y -> assembleIsObj mp (TSIntersection y)
    TSPrimType _ -> Nothing
  where
    mp = isObjKeyVals x

isObjKeyVals
    :: TSType p 'IsObj a
    -> Map Text (Some (Pre a (TSType_ p)))
isObjKeyVals = \case
    TSObject ts -> splitKeyVal ts
    TSIntersection (PreT ts) -> hfoldMap
      (\(f :>$<: t) -> isObjKeyVals t <&> \case Some p -> Some (mapPre f p))
      ts
    TSNamedType (TSNamed{..} :$ ps) -> case tsnType of
      TSNFunc tf -> isObjKeyVals (tsApply tf ps)

assembleIsObj
    :: forall a b. ()
    => Map Text (Some (Pre a (TSType_ 'Z)))
    -> TSType 'Z 'IsObj b
    -> Maybe (Assign a b)
assembleIsObj mp = \case
    TSObject ts -> assembleKeyVal mp ts
    TSIntersection ts -> fmap unwrapAssign . getCompose $ interpret (Compose . fmap WrapAssign . assembleIsObj mp) ts
    TSNamedType (TSNamed{..} :$ ps) -> case tsnType of
      TSNFunc tf -> assembleIsObj mp (tsApply tf ps)

assembleKeyVal
    :: forall a b. ()
    => Map Text (Some (Pre a (TSType_ 'Z)))
    -> TSKeyVal 'Z b
    -> Maybe (Assign a b)
assembleKeyVal mp (PreT p) = unwrapAssign <$> go p
  where
    go :: Ap (Pre d (ObjMember (TSType_ 'Z))) c -> Maybe (WrappedAssign a c)
    go = \case
      Pure x -> Just $ pure x
      Ap (_ :>$<: ObjMember{..}) xs -> do
        Some (q :>$<: TSType_ u) <- M.lookup objMemberKey mp
        -- if the original is Non-Nullable, we can assign it to anything
        -- if the original is Nullable, we can only assign it to Nullable
        -- TODO: this is now wrong because required assignment to nullable is
        -- different from optional assignment
        let objVal = case objMemberVal of
              L1 t                      -> t
              R1 (ILan g h (TSType_ t)) -> TSType_ $ invmap g h $ toNullable t
        (`withTSType_` objVal) $ \t -> do
          rx  <- WrapAssign <$> reAssign u t
          rxs <- go xs
          pure $ rxs <*> lmap q rx

