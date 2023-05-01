{-# LANGUAGE LambdaCase #-}

module Hs2Agda.Plugin.CodeGen
  where

import Hs2Agda.Plugin.Types
import Hs2Agda.Plugin.Scan

import GHC.Plugins
import GHC.Hs
import Control.Monad (forM_, unless, when, forM, (<=<))
import Control.Concurrent (putMVar)
import Data.List (intercalate, intersperse, isPrefixOf)
import Data.Maybe (catMaybes, mapMaybe)
import Data.Text (Text, pack, unpack)
import qualified NeatInterpolation as NI (text)
import System.Directory
import Data.Bool (bool)
import qualified Data.Foldable as NonEmpty
import GHC.Core.Multiplicity (Scaled(..))

vcatsp = vcat . intersperse (text "")
hcatsp = foldr (<+>) empty

-- data CodeGenResult = CodeGenResult
--   { dataTypes :: SDoc
--   , binders   :: SDoc
--   , rawCode   :: SDoc
--   }

-- codeGenAnns
--   :: ModuleEnv [HS2AgdaAnn]
--   -> NameEnv [HS2AgdaAnn]
--   -> [TyCon]
--   -> [CoreBind]
--   -> CodeGenResult
-- codeGenAnns menv nenv tcs bs =
--   CodeGenResult
--     (vcatsp (codeGenData nenv tcs))
--     (vcatsp (codeGenBinders nenv bs))
--     (vcatsp (ppRawAgda (concat (moduleEnvElts menv))))
--   where
--     ppRawAgda = map (text . unpack) . mapMaybe getAgdaRaw

-- codeGenData :: NameEnv [HS2AgdaAnn] -> [TyCon] -> [SDoc]
-- codeGenData env =
--   mapMaybe (\tc -> if elemNameEnv (tyConName tc) env
--                    then Just (ppAgdaData tc)
--                    else Nothing)

-- codeGenBndr :: NameEnv [HS2AgdaAnn] -> CoreBndr -> CoreExpr -> Maybe SDoc
-- codeGenBndr env b e = case anns of
--   [HS2Agda] -> Just (ppAgdaTopLevel b e)
--   _         -> Nothing
--   where
--     anns = lookupWithDefaultUFM_Directly env [] (varUnique b)

-- codeGenBinders :: NameEnv [HS2AgdaAnn] -> [CoreBind] -> [SDoc]
-- codeGenBinders env = mapMaybe (uncurry (codeGenBndr env) <=< unpackBndr)
--   where
--     unpackBndr :: CoreBind -> Maybe (CoreBndr, CoreExpr)
--     unpackBndr = \case
--       NonRec b e   -> Just (b, e)
--       Rec [(b, e)] -> Just (b, e)
--       _            -> Nothing


ppMutual :: Bool -> SDoc -> SDoc
ppMutual True d = vcat [ text "mutual", nest 2 d ]
ppMutual False d = d

ppPrivate :: SDoc -> SDoc
ppPrivate d
  | isEmpty defaultSDocContext d = empty
  | otherwise = vcat [ text "private", nest 2 d ]

ppInstance :: SDoc -> SDoc
ppInstance d = vcat [ text "instance", nest 2 d ]

ppUnifiedBind :: UnifiedBind -> SDoc
ppUnifiedBind ub = ppMutual (length ubl > 1) ubDoc
  where
    ubl   = NonEmpty.toList ub
    ubDoc = vcatsp (map (uncurry ppAgdaTopLevel) ubl)

ppInstanceUnifiedBind :: UnifiedBind -> SDoc
ppInstanceUnifiedBind ((b,e) :| bs) = ppMutual (notNull bs) . vcatsp $
  [ ppInstance (ppAgdaTopLevel b e)
  , ppPrivate . vcatsp $ map (uncurry ppAgdaTopLevel) bs
  ]

ppActiveBind :: ActiveBind -> SDoc
ppActiveBind = \case
  Annotated ub -> ppUnifiedBind ub
  Instance ubs ub ->
    let ubsDoc = ppPrivate (vcatsp (map ppUnifiedBind ubs))
    in vcatsp [ubsDoc, ppInstanceUnifiedBind ub]

ppWholeModule
  :: ModuleName
  -> [ModuleName]
  -> [TyCon]
  -> [ActiveBind]
  -> SDoc
ppWholeModule m imps tcs bs = vcatsp $
  [ text "module" <+> ppr m <+> text "where"
  , vcat (map (text "open import" <+>) imports)
  ] ++ map ppAgdaData tcs
    ++ map ppActiveBind bs
  where imports = text "Hs2Agda.Prelude" : map ppr imps

-- ppWholeModule :: ModuleName -> [ModuleName] -> CodeGenResult -> SDoc
-- ppWholeModule m imps cgr =
--   vcatsp
--     [ text "module" <+> ppr m <+> text "where"
--     , vcat (map (text "open import" <+>) imports)
--     , dataTypes cgr
--     , binders cgr
--     , rawCode cgr
--     ]
--   where imports = text "HsPrelude" : map ppr imps

ppAgdaData :: TyCon -> SDoc
ppAgdaData tc = toAgdaData (tyConName tc) (tyConTyVars tc) dcsinfo
  where
    dcs = tyConDataCons tc
    dcsinfo = fmap (\dc ->
                      let (_,_,_,_,x,y) = dataConFullSig dc
                      in (dataConName dc, x, y)) dcs

ppTyBndr :: Var -> SDoc
ppTyBndr v = braces (ppr v)

-- ppAgdaVar :: Var -> SDoc
-- ppAgdaVar v
--   -- | isDFunId v = ppr (localiseId v)
--   | isDerivedOccName (occName v) = ppr (varUnique v, text (getOccString v))
--   | otherwise = ppr v

ppAgdaRhsVar :: Var -> SDoc
ppAgdaRhsVar v
  | isDFunId v = empty
  | isClassCtor (getOccString v) = text ("Mk" ++ drop 2 (getOccString v))
  | isDerivedOccName (occName v) = ppr (varUnique v)
  | otherwise = ppr v
  where
    isClassCtor :: String -> Bool
    isClassCtor = Data.List.isPrefixOf "C:"

ppAgdaLhsVar :: Var -> SDoc
ppAgdaLhsVar v
--  | isDFunId v = text "_"
  | isDerivedOccName (occName v) = ppr (varUnique v)
  | otherwise = ppr v

ppAgdaDecl :: Var -> SDoc
ppAgdaDecl v = hcatsp [ppAgdaLhsVar v, text ":", ppVars vars, ppr ty]
  where
    ppVars [] = empty
    ppVars vs = hsep $ [text "{"] ++ ppUniquedIds vs [] ++ [text ": Set } ->"]
    (vars, ty) = splitForAllTyCoVars (varType v)
    -- there should be a better way to do this
    ppUniquedIds :: [Id] -> [String] -> [SDoc]
    ppUniquedIds = flip foldr (const []) $ \i h s ->
      let str = getOccString i
          mult = length (filter (str ==) s)
          uniqued = text (str ++ (if mult == 0 then "" else show mult))
      in uniqued : h (str : s)

ppAgdaBind :: Var -> CoreExpr -> SDoc
ppAgdaBind v e = vcat [ hcatsp [ppAgdaLhsVar v, text "="], nest 2 (ppAgdaExpr e) ]

ppAgdaTopLevelFunDef :: Var -> CoreExpr -> SDoc
ppAgdaTopLevelFunDef v e = vcat
  -- [ hcatsp $ [ppAgdaLhsVar v] ++ map ppTyBndr tyvs ++ map ppr vs ++ [text "="]
  [ hcatsp $ [ppAgdaLhsVar v] ++ map ppr vs ++ [text "="]
  , nest 2 (ppAgdaExpr e')
  ]
  where (tyvs, vs, e') = collectTyAndValBinders e

ppAgdaTopLevel :: Var -> Expr Var -> SDoc
ppAgdaTopLevel v e = vcat
  [ ppAgdaDecl v
  , ppAgdaTopLevelFunDef v e
  ]

ppLamExpr :: [Id] -> CoreExpr -> SDoc
ppLamExpr [] e = ppAgdaExpr e
ppLamExpr vs e = vcat
  [ hsep $ [text "\\"] ++ map ppr vs ++ [text "->"]
  , nest 2 (ppAgdaExpr e)
  ]

ppAgdaExpr :: Expr Var -> SDoc
ppAgdaExpr e@(Lam _ _) = ppLamExpr vs e'
  where (_, vs, e') = collectTyAndValBinders e
-- ppAgdaExpr (Lam b e) = vcat
--   [ text "\\" <+> ppVar b <+> text "->"
--   , nest 2 (ppAgdaExpr e)
--   ]
--   where ppVar b = if isTyVar b then text "{" <+> ppr b <+> text "}" else ppr b
ppAgdaExpr (Case e _ _ alts) = vcat $
  (text "case" <+> ppr e <+> text "of \\ where") :
  map (nest 2 . toAgdaAlt) alts
  where
    toAgdaAlt (Alt c vs e) = vcat
      [ parens (ppr c <+> hsep (map ppr vs)) <+> text "->"
      , nest 2 (ppAgdaExpr e)
      ]
ppAgdaExpr e@(App _ _)
  | isDFunExpr f = empty
  | otherwise = ppAppExpr f args
  where (f, args) = collectArgs e
ppAgdaExpr (Type t) = ppTypeExpr t
ppAgdaExpr (Var v) = ppAgdaRhsVar v
ppAgdaExpr (Let (NonRec b e) e') = vcat
  [ text "let" <+> vcat [ppAgdaDecl b, ppAgdaBind b e]
  , text "in" <+> ppAgdaExpr e'
  ]
ppAgdaExpr e = panic "HS2Agda: unsupported core expression" -- ppr e

ppAppExpr :: CoreExpr -> [CoreExpr] -> SDoc
ppAppExpr f args = hcatsp
  $ cparen (shouldParen f) (ppAgdaExpr f)
  : map (\a -> cparen (shouldParen a) (ppAgdaExpr a)) args
-- ppAppExpr f args = hcatsp $ cparen (shouldParen f) (ppAgdaExpr f) : map (\a -> cparen (shouldParen a) (ppAgdaExpr a)) args


ppTypeExpr :: Type -> SDoc
ppTypeExpr = const empty
-- ppTypeExpr t = text "{" <+> ppr t <+> text "}"

isDFunExpr :: CoreExpr -> Bool
isDFunExpr (Var v) = isDFunId v
isDFunExpr _ = False

toAgdaData :: Name -> [TyVar] -> [(Name, [Scaled Type], Type)] -> SDoc
toAgdaData n vs dcs = vcat
  [ hsep [text "data", pprNameUnqualified n, text "(", hsep vs', text ": Set ) : Set where" ]
  , nest 2 (vcat (map ppCtor dcs))
  ]
  where
    vs' = map ppr vs

    ppCtor :: (Name, [Scaled Type], Type) -> SDoc
    ppCtor (n, args, cod) =
      hsep $ [pprNameUnqualified n, text ":"]
          ++ intersperse (text "->") (map (parens . ppr) args ++ [ppr cod])

shouldParen :: CoreExpr -> Bool
shouldParen = \case
  (Var _) -> False
  (Type _) -> False
  e@(App _ _) -> not (isDFunExpr (fst (collectArgs e)))
  _ -> True
