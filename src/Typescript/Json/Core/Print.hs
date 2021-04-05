{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE EmptyCase           #-}
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
  , ppNamedBase
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
import           Data.Set                          (Set)
import           Data.Text                         (Text)
import           Data.Type.Nat
import           Data.Vec.Lazy                     (Vec(..))
import           Typescript.Json.Types
import           Typescript.Json.Types.Combinators
import           Typescript.Json.Types.Sing
import qualified Control.Applicative.Lift          as Lift
import qualified Data.DList                        as DL
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
    TSNumber       -> "number"
    TSBigInt       -> "bigint"
    TSString       -> "string"
    TSUnknown      -> "unknown"
    TSAny          -> "any"

ppBase :: TSBase a -> PP.Doc x
ppBase = \case
    TSBoolean      -> "boolean"
    TSStringLit t  -> PP.pretty (show t)
    TSNumericLit n -> ppScientific n
    TSBigIntLit n  -> PP.pretty n
    TSVoid         -> "void"
    TSUndefined    -> "undefined"
    TSNull         -> "null"
    TSNever        -> "never"


ppNamedBase :: Text -> TSNamedBase a -> PP.Doc x
ppNamedBase n = \case
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
      TSTuple ts  -> PP.encloseSep "[ " " ]" ", " (htoList (withTSType_ (go ps)) ts)
      TSObject ts -> PP.encloseSep "{ " " }" ", " $
        htoList
          ( getConst . interpretObjMember
              (\ro k x -> Const . roText ro $ PP.pretty k <> ":"  PP.<+> withTSType_ (go ps) x)
              (\ro k x -> Const . roText ro $ PP.pretty k <> "?:" PP.<+> withTSType_ (go ps) x)
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
      TSTransformType tf -> getConst $ (`interpret` tf) $ \case
        TSPartial t -> Const $ "Partial<" <> go ps t <> ">"
        TSReadOnly t -> Const $ "ReadOnly<" <> go ps t <> ">"
        TSPickPartial o ks _ -> Const $
          "Pick" <> PP.encloseSep "<" ">" ","
            [ "Partial<" <> go ps o <> ">"
            , go ps ks
            ]
        TSOmitPartial o ks _ -> Const $
          "Omit" <> PP.encloseSep "<" ">" ","
            [ "Partial<" <> go ps o <> ">"
            , go ps ks
            ]
        TSStringManipType sm t _ -> Const $ ppStringManip sm
                                        <> "<" <> go ps t <> ">"
      TSPrimType PS{..} -> ppPrim psItem
      TSBaseType (ICoyoneda _ _ x) -> ppBase x
    roText = \case
      Mutable  -> id
      ReadOnly -> ("readonly" PP.<+>)

ppStringManip :: TSStringManip -> PP.Doc x
ppStringManip = \case
    TSUppercase -> "Uppercase"
    TSLowercase -> "Lowercase"
    TSCapitalize -> "Capitalize"
    TSUncapitalize -> "Uncapitalize"

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
    TSNBaseType (ICoyoneda _ _ x) -> ppNamedBase tsnName x

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
flattenNamedType ps t = execState (flattenNamedType_ ps S.empty t) M.empty

-- | Ignores the top level type, so why even bother?
flattenType
    :: Vec p Text
    -> TSType p k a
    -> Map Text (Set Text, PP.Doc x)
flattenType ps t = execState (flattenType_ ps S.empty t) M.empty

flattenNamedType_
    :: forall p k a as es x. ()
    => Vec p Text
    -> Set Text                 -- ^ types it is currently named under
    -> TSNamed p k as es a
    -> State (Map Text (Set Text, PP.Doc x)) (Set Text)
flattenNamedType_ ps seen tsn@TSNamed{..} = case tsnType of
    TSNFunc tsf -> do
      deps <- flattenType_ (tsfParams tsf Vec.++ ps) (S.insert tsnName seen) (tsApplyVar tsf)
      modify $ M.insert tsnName (deps, pp)
      pure deps
    TSNBaseType _ -> do
      modify $ M.insert tsnName (S.empty, pp)
      pure S.empty
  where
    pp = ppNamed' ps tsn

-- | TODO: stop if it is a recursive reference
flattenType_
    :: forall p k a x. ()
    => Vec p Text
    -> Set Text                 -- ^ types it is currently named under
    -> TSType p k a
    -> State (Map Text (Set Text, PP.Doc x)) (Set Text)
flattenType_ ps seen = go
  where
    go  :: forall j b. ()
        => TSType p j b
        -> State (Map Text (Set Text, PP.Doc x)) (Set Text)
    go = \case
      TSArray ts   -> hfoldMap SOP.unK <$> htraverse (fmap K . go) ts
      TSTuple ts   -> hfoldMap SOP.unK <$> htraverse (withTSType_ (fmap K . go)) ts
      TSObject ts  -> hfoldMap (hfoldMap SOP.unK) <$> htraverse (htraverse (withTSType_ (fmap K . go))) ts
      TSSingle t   -> go t
      TSUnion ts   -> hfoldMap SOP.unK <$> htraverse (withTSType_ (fmap K . go)) ts
      TSNamedType (tsn@(TSNamed nm _) :$ args) -> do
        -- should we guard this too?
        deps1 <- hfoldMap2 getConstF <$> htraverse2 (\(Arg_ Arg{..}) -> ConstF <$> go argType) args
        deps2 <- if nm `S.member` seen
          then pure S.empty
          else flattenNamedType_ ps seen tsn
        pure $ deps1 <> deps2
      TSVar _      -> pure S.empty
      TSIntersection ts -> hfoldMap SOP.unK <$> htraverse (fmap K . go) ts
      TSTransformType tf -> fmap (hfoldMap SOP.unK) $ (`htraverse` tf) $ \case
        TSPartial t -> K <$> go t
        TSReadOnly t -> K <$> go t
        TSPickPartial o ks _ -> fmap K $ (<>) <$> go o <*> go ks
        TSOmitPartial o ks _ -> fmap K $ (<>) <$> go o <*> go ks
        TSStringManipType _ t _ -> K <$> go t
      TSPrimType _ -> pure S.empty
      TSBaseType _ -> pure S.empty

