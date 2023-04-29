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
  [HS2Agda] -> Just (toAgdaTopLevel b e)
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

-- TODO: replace with functions already defined in GHC.Core module
splitTypeLambdas :: CoreExpr -> ([Var], CoreExpr)
splitTypeLambdas x@(Lam b e)
  | isTyVar b = let (vs, e') = splitTypeLambdas e in (b : vs, e')
  | otherwise = ([], x)
splitTypeLambdas e = ([], e)

ppTyBndr :: Var -> SDoc
ppTyBndr v = braces (ppr v)

ppAgdaDecl :: Var -> SDoc
ppAgdaDecl v = hcatsp [ppr v, text ":", ppVars vars, ppr ty]
  where
    ppVars [] = empty
    ppVars vs = text "{" <+> hsep (map ppr vs) <+> text ": Set } ->"
    (vars, ty) = splitForAllTyCoVars (varType v)

ppAgdaTopLevel :: Var -> SDoc -> CoreExpr -> SDoc
ppAgdaTopLevel v aux e = vcat
  [ hcatsp [ppr v, aux, text "="]
  , nest 2 (toAgdaExpr e)
  ]

toAgdaTopLevel :: Var -> CoreExpr -> SDoc
toAgdaTopLevel v e = toAgdaBinder v (hcat (map ppTyBndr tyVars)) e'
  where  (tyVars, e') = splitTypeLambdas e

toAgdaBinder :: Var -> SDoc -> Expr Var -> SDoc
toAgdaBinder v aux e = vcat
  [ ppAgdaDecl v
  , ppAgdaTopLevel v aux e
  ]

toAgdaExpr :: Expr Var -> SDoc
toAgdaExpr (Lam b e) = vcat
  [ text "\\" <+> ppVar b <+> text "->"
  , nest 2 (toAgdaExpr e)
  ]
  where ppVar b = if isTyVar b then text "{" <+> ppr b <+> text "}" else ppr b
toAgdaExpr (Case e _ _ alts) = vcat $
  (text "case" <+> ppr e <+> text "of \\ where") :
  map (nest 2 . toAgdaAlt) alts
  where
    toAgdaAlt (Alt c vs e) = vcat
      [ parens (ppr c <+> hsep (map ppr vs)) <+> text "->"
      , nest 2 (toAgdaExpr e)
      ]
toAgdaExpr (App e arg) = cparen b1 (toAgdaExpr e) <+> cparen b2 (toAgdaExpr arg)
  where
    b1 = shouldParen e
    b2 = shouldParen arg
toAgdaExpr (Type t) = text "{" <+> ppr t <+> text "}"
toAgdaExpr (Var v) = ppr v
toAgdaExpr (Let (NonRec b e) e') = vcat
  [ text "let" <+> toAgdaBinder b empty e
  , text "in" <+> toAgdaExpr e'
  ]
toAgdaExpr e = panic "HS2Agda: unsupported core expression" -- ppr e

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
