{-# LANGUAGE LambdaCase #-}

module Hs2Agda.Plugin.CodeGen
  where

import Hs2Agda.Plugin.Types

import GHC.Plugins
import GHC.Hs
import Data.Data (Data)
import Control.Monad (forM_, unless, when, forM, (<=<))
import Control.Concurrent (putMVar)
import GHC.Types.Name
import Data.List (intercalate, intersperse)
import Data.Maybe (catMaybes, mapMaybe)
import Data.Text (Text, pack, unpack)
import qualified NeatInterpolation as NI (text)
import System.Directory
import Data.Bool (bool)

vcatsp = vcat . intersperse (text "")
hcatsp = foldr (<+>) empty

data CodeGenResult = CodeGenResult
  { dataTypes :: SDoc
  , binders   :: SDoc
  , rawCode   :: SDoc
  }

codeGenAnns
  :: ModuleEnv [HS2AgdaAnn]
  -> NameEnv [HS2AgdaAnn]
  -> [TyCon]
  -> [CoreBind]
  -> CodeGenResult
codeGenAnns menv nenv tcs bs =
  CodeGenResult
    (vcatsp (codeGenData nenv tcs))
    (vcatsp (codeGenBinders nenv bs))
    (vcatsp (ppRawAgda (concat (moduleEnvElts menv))))
  where
    ppRawAgda = map (text . unpack) . mapMaybe getAgdaRaw

codeGenData :: NameEnv [HS2AgdaAnn] -> [TyCon] -> [SDoc]
codeGenData env =
  mapMaybe (\tc -> if elemNameEnv (tyConName tc) env
                   then Just (ppAgdaData tc)
                   else Nothing)

codeGenBndr :: NameEnv [HS2AgdaAnn] -> CoreBndr -> CoreExpr -> Maybe SDoc
codeGenBndr env b e = case anns of
  [HS2Agda] -> Just (ppAgdaTopLevel b e)
  _         -> Nothing
  where
    anns = lookupWithDefaultUFM_Directly env [] (varUnique b)


codeGenBinders :: NameEnv [HS2AgdaAnn] -> [CoreBind] -> [SDoc]
codeGenBinders env = mapMaybe (uncurry (codeGenBndr env) <=< unpackBndr)
  where
    unpackBndr :: CoreBind -> Maybe (CoreBndr, CoreExpr)
    unpackBndr = \case
      NonRec b e   -> Just (b, e)
      Rec [(b, e)] -> Just (b, e)
      _            -> Nothing

ppWholeModule :: ModuleName -> [ModuleName] -> CodeGenResult -> SDoc
ppWholeModule m imps cgr =
  vcatsp
    [ text "module" <+> ppr m <+> text "where"
    , vcat (map (text "open import" <+>) imports)
    , dataTypes cgr
    , binders cgr
    , rawCode cgr
    ]
  where imports = text "HsPrelude" : map ppr imps

ppAgdaData :: TyCon -> SDoc
ppAgdaData tc = toAgdaData (tyConName tc) (tyConTyVars tc) dcsinfo
  where
    dcs = tyConDataCons tc
    dcsinfo = fmap (\dc ->
                      let (_,_,_,_,x,y) = dataConFullSig dc
                      in (dataConName dc, x, y)) dcs

ppTyBndr :: Var -> SDoc
ppTyBndr v = braces (ppr v)

ppAgdaDecl :: Var -> SDoc
ppAgdaDecl v = hcatsp [ppr v, text ":", ppVars vars, ppr ty]
  where
    ppVars [] = empty
    ppVars vs = text "{" <+> hsep (map ppr vs) <+> text ": Set } ->"
    (vars, ty) = splitForAllTyCoVars (varType v)

ppAgdaBind :: Var -> CoreExpr -> SDoc
ppAgdaBind v e = vcat [ hcatsp [ppr v, text "="], nest 2 (ppAgdaExpr e) ]

ppAgdaTopLevelFunDef :: Var -> CoreExpr -> SDoc
ppAgdaTopLevelFunDef v e = vcat
  [ hcatsp $ [ppr v] ++ map ppTyBndr tyvs ++ map ppr vs ++ [text "="]
  , nest 2 (ppAgdaExpr e')
  ]
  where (tyvs, vs, e') = collectTyAndValBinders e

ppAgdaTopLevel :: Var -> Expr Var -> SDoc
ppAgdaTopLevel v e = vcat
  [ ppAgdaDecl v
  , ppAgdaTopLevelFunDef v e
  ]

ppAgdaExpr :: Expr Var -> SDoc
ppAgdaExpr (Lam b e) = vcat
  [ text "\\" <+> ppVar b <+> text "->"
  , nest 2 (ppAgdaExpr e)
  ]
  where ppVar b = if isTyVar b then text "{" <+> ppr b <+> text "}" else ppr b
ppAgdaExpr (Case e _ _ alts) = vcat $
  (text "case" <+> ppr e <+> text "of \\ where") :
  map (nest 2 . toAgdaAlt) alts
  where
    toAgdaAlt (Alt c vs e) = vcat
      [ parens (ppr c <+> hsep (map ppr vs)) <+> text "->"
      , nest 2 (ppAgdaExpr e)
      ]
ppAgdaExpr (App e arg) = cparen b1 (ppAgdaExpr e) <+> cparen b2 (ppAgdaExpr arg)
  where
    b1 = shouldParen e
    b2 = shouldParen arg
ppAgdaExpr (Type t) = text "{" <+> ppr t <+> text "}"
ppAgdaExpr (Var v) = ppr v
ppAgdaExpr (Let (NonRec b e) e') = vcat
  [ text "let" <+> vcat [ppAgdaDecl b, ppAgdaBind b e]
  , text "in" <+> ppAgdaExpr e'
  ]
ppAgdaExpr e = panic "HS2Agda: unsupported core expression" -- ppr e

toAgdaData :: Name -> [TyVar] -> [(Name, [Scaled Type], Type)] -> SDoc
toAgdaData n vs dcs =
  ( text "data" <+> pprNameUnqualified n <+>
      text "(" <+> sep vs' <+> text ": Set ) : Set where" ) $+$
  nest 2 (vcat (map ppCtor dcs))
  where
    vs' = map ppr vs
    ppCtor :: (Name, [Scaled Type], Type) -> SDoc
    ppCtor (n, args, cod) =
      sep $ [pprNameUnqualified n, text ":"] ++ intersperse (text "->")
        (map (parens . ppr) args ++ [ppr cod])

shouldParen :: CoreExpr -> Bool
shouldParen = \case
  (Var _) -> False
  (Type _) -> False
  _ -> True
