{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}

module Typescript.Json.Core.Print (
    ppType 
  , ppEnumLit
  , ppNamedPrim
  , ppNamed
  , ppNamed'
  , typeExports_
  , typeExports
  , typeExports'
  , namedTypeExports_
  , namedTypeExports
  , namedTypeExports'
  , ppMap
  , flattenNamedType
  , flattenType
  , flattenType_
  ) where

import           Control.Applicative
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Foldable
import           Data.Functor.Combinator hiding    (Comp(..))
import           Data.Map                          (Map)
import           Data.Maybe
import           Data.Ord
import           Data.SOP                          (K(..))
import           Data.Scientific                   (Scientific, toBoundedInteger)
import qualified Data.DList as DL
import           Data.Set                          (Set)
import           Data.Text                         (Text)
import           Data.Type.Nat
import           Data.Vec.Lazy                     (Vec(..))
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators
import           Typescript.Json.Types.SNat
import qualified Control.Applicative.Lift          as Lift
import qualified Data.Graph.Inductive.Graph        as FGL
import qualified Data.Graph.Inductive.PatriciaTree as FGL
import qualified Data.Graph.Inductive.Query.DFS    as FGL
import qualified Data.Map                          as M
import qualified Data.SOP                          as SOP
import qualified Data.Set                          as S
import qualified Data.Vec.Lazy                     as Vec
import qualified Prettyprinter                     as PP



ppScientific :: Scientific -> PP.Doc x
ppScientific n = maybe (PP.pretty (show n)) PP.pretty
               . toBoundedInteger @Int
               $ n

ppEnumLit :: EnumLit -> PP.Doc x
ppEnumLit = \case
    ELString t -> PP.pretty (show t)
    ELNumber n -> ppScientific n

ppPrim :: TSPrim a -> PP.Doc x
ppPrim = \case
    TSBoolean      -> "boolean"
    TSNumber       -> "number"
    TSBigInt       -> "bigint"
    TSString       -> "string"
    TSStringLit t  -> PP.pretty (show t)
    TSNumericLit n -> ppScientific n
    TSBigIntLit n  -> PP.pretty n
    TSUnknown      -> "unknown"
    TSAny          -> "any"
    TSVoid         -> "void"
    TSUndefined    -> "undefined"
    TSNull         -> "null"
    TSNever        -> "never"

ppNamedPrim :: Text -> TSNamedPrim a -> PP.Doc x
ppNamedPrim n = \case
    TSEnum es    -> PP.fillSep
      [ "enum"
      , PP.pretty n
      , PP.encloseSep "{" "}" ","
          [ PP.pretty e PP.<+> "=" PP.<+> ppEnumLit x
          | (e, x) <- toList es
          ]
      ]

ppType
    :: TSType 'Z k a
    -> PP.Doc x
ppType = ppType' VNil

ppType'
    :: forall p k a x. ()
    => Vec p Text
    -> TSType p k a
    -> PP.Doc x
ppType' = go
  where
    go :: Vec q Text -> TSType q j b -> PP.Doc x
    go ps = \case
      TSArray t   -> getConst (interpretILan (Const . go ps) t) <> "[]"
      -- TODO: hm, should this be not a primitive?
      -- i guess in a sense it does matter because of optional chaining?
      TSNullable t -> getConst (interpretILan (Const . go ps) t) PP.<+> "| null"
      TSTuple ts  -> PP.encloseSep "[ " " ]" ", " (htoList (withTSType_ (go ps)) ts)
      TSObject ts -> PP.encloseSep "{ " " }" ", " $
        htoList
          ( getConst . interpretObjMember
              (\k x -> Const (PP.pretty k <> ":"  PP.<+> withTSType_ (go ps) x ))
              (\k x -> Const (PP.pretty k <> "?:" PP.<+> withTSType_ (go ps) x))
          )
          ts
      TSSingle ts -> go ps ts
      TSUnion ts  -> PP.encloseSep "" "" " | " (htoList (withTSType_ (go ps)) ts)
      -- this is the benefit of delaying application
      TSNamedType (TSNamed nm _ :$ xs) ->
        let args = DL.toList $ hfoldMap2 (\(Arg_ Arg{..}) -> DL.singleton (go ps argType)) xs
        in  PP.pretty nm <>
              (if null args then ""
                            else PP.encloseSep "<" ">" "," args
              )
      TSVar i -> PP.pretty (ps Vec.! i)
      TSIntersection ts  -> PP.encloseSep "" "" " & " (htoList (go ps) ts)
      TSPrimType PS{..} -> ppPrim psItem

ppNamed
    :: TSNamed 'Z k as es a
    -> PP.Doc x
ppNamed = ppNamed' VNil

ppNamed'
    :: Vec p Text
    -> TSNamed p k as es a
    -> PP.Doc x
ppNamed' ps TSNamed{..} = case tsnType of
    TSNFunc tsf -> case tsf of
      TSGeneric vs _ ->
        let args = prodVec2 paramName vs
        in  PP.hsep [
              "type"
                PP.<+> PP.pretty tsnName
                PP.<> (if null args then ""
                                    else PP.encloseSep "<" ">" "," (PP.pretty <$> toList args)
                      )
            , "="
            , ppType' (args Vec.++ ps) (tsApplyVar tsf)
            ]
      TSGenericInterface vs _ _ ext _ ->
        let args = prodVec2 paramName vs
        in  PP.hsep . catMaybes $ [
              Just "interface"
            , Just $ PP.pretty tsnName
                PP.<> (if null args then ""
                                    else PP.encloseSep "<" ">" "," (PP.pretty <$> toList args)
                      )
            , case ext of
                Lift.Pure _ -> Nothing
                Lift.Other (tf :? _) -> Just $
                  "extends" PP.<+> ppNamed' ps tf
            , Just $ ppType' (args Vec.++ ps) (tsApplyVar tsf)
            ]
    TSNPrimType PS{..} -> ppNamedPrim tsnName psItem

typeExports_
    :: TSType_ 'Z a
    -> PP.Doc x
typeExports_ = withTSType_ typeExports

typeExports
    :: TSType 'Z k a
    -> PP.Doc x
typeExports = typeExports' VNil

typeExports'
    :: Vec p Text
    -> TSType p k a
    -> PP.Doc x
typeExports' ps = ppMap . flattenType ps

namedTypeExports_
    :: TSNamed_ 'Z as es a
    -> PP.Doc x
namedTypeExports_ = withTSNamed_ namedTypeExports

namedTypeExports
    :: TSNamed 'Z k as es a
    -> PP.Doc x
namedTypeExports = namedTypeExports' VNil

namedTypeExports'
    :: Vec p Text
    -> TSNamed p k as es a
    -> PP.Doc x
namedTypeExports' ps = ppMap . flattenNamedType ps

ppMap
    :: forall x. ()
    => Map Text (Set Text, PP.Doc x)
    -> PP.Doc x
ppMap (M.mapKeys Down->mp) = PP.vcat $
    ("export" PP.<+>) <$> FGL.topsort' graph
  where
    nodes = zip [0..] (toList mp)
    graph :: FGL.Gr (PP.Doc x) ()
    graph = FGL.mkGraph
      (second snd <$> nodes)
      [ (i, j, ())
      | (i, (refs, _)) <- nodes
      , r <- S.toList refs
      , j <- maybeToList $ M.lookupIndex (Down r) mp
      ]


-- | Pull out all of the named types to be top-level type declarations, and
-- have create a map of all of those declarations.
flattenNamedType
    :: Vec p Text
    -> TSNamed p k as es a
    -> Map Text (Set Text, PP.Doc x)
flattenNamedType ps t = execState (flattenNamedType_ ps t) M.empty

-- | Ignores the top level type, so why even bother?
flattenType
    :: Vec p Text
    -> TSType p k a
    -> Map Text (Set Text, PP.Doc x)
flattenType ps t = execState (flattenType_ ps t) M.empty

flattenNamedType_
    :: forall p k a as es x. ()
    => Vec p Text
    -> TSNamed p k as es a
    -> State (Map Text (Set Text, PP.Doc x)) (Set Text)
flattenNamedType_ ps tsn@TSNamed{..} = case tsnType of
    TSNFunc tsf -> do
      deps <- flattenType_ (tsfParams tsf Vec.++ ps) (tsApplyVar tsf)
      modify $ M.insert tsnName (deps, pp)
      pure deps
    TSNPrimType PS{..} -> do
      modify $ M.insert tsnName (S.empty, pp)
      pure S.empty
  where
    pp = ppNamed' ps tsn

flattenType_
    :: forall p k a x. ()
    => Vec p Text
    -> TSType p k a
    -> State (Map Text (Set Text, PP.Doc x)) (Set Text)
flattenType_ ps = go
  where
    go  :: forall j b. ()
        => TSType p j b
        -> State (Map Text (Set Text, PP.Doc x)) (Set Text)
    go = \case
      TSArray ts   -> hfoldMap SOP.unK <$> htraverse (fmap K . go) ts
      TSNullable t -> hfoldMap SOP.unK <$> htraverse (fmap K . go) t
      TSTuple ts   -> hfoldMap SOP.unK <$> htraverse (withTSType_ (fmap K . go)) ts
      TSObject ts  -> hfoldMap (hfoldMap SOP.unK) <$> htraverse (htraverse (withTSType_ (fmap K . go))) ts
      TSSingle t   -> go t
      TSUnion ts   -> hfoldMap SOP.unK <$> htraverse (withTSType_ (fmap K . go)) ts
      TSNamedType (tsn :$ args) -> do
        deps1 <- hfoldMap2 getConstF <$> htraverse2 (\(Arg_ Arg{..}) -> ConstF <$> go argType) args
        deps2 <- flattenNamedType_ ps tsn
        pure $ deps1 <> deps2
      TSVar _      -> pure S.empty
      TSIntersection ts -> hfoldMap SOP.unK <$> htraverse (fmap K . go) ts
      TSPrimType _ -> pure S.empty

