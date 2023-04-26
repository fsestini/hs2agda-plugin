module Hs2Agda.Plugin.CodeGen where

import GHC.Plugins
import GHC.Hs
import Data.Data (Data)
import Control.Monad (forM_, unless, when, forM)
import Control.Concurrent (putMVar)
import GHC.Types.Name
import Data.List (intercalate, intersperse)
import Data.Maybe (catMaybes, mapMaybe)
import Data.Text (Text, pack, unpack)
import qualified NeatInterpolation as NI (text)
import System.Directory
import Data.Bool (bool)

vcatsp = vcat . intersperse (text "")

data CodeGenResult = CodeGenResult
  { dataTypes :: SDoc
  , binders   :: SDoc
  , rawCode   :: SDoc
  }

ppWholeModule :: ModuleName -> [ModuleName] -> CodeGenResult -> SDoc
ppWholeModule m imps cgr =
  vcatsp
    $ (text "module" <+> ppr m <+> text "where")
    : map ((text "open import" <+>) . ppr) imps ++
    [ dataTypes cgr
    , binders cgr
    , rawCode cgr
    ]

ppAgdaData :: TyCon -> SDoc
ppAgdaData tc = toAgdaData (tyConName tc) (tyConTyVars tc) dcsinfo
  where
    dcs = tyConDataCons tc
    dcsinfo = fmap (\dc ->
                      let (_,_,_,_,x,y) = dataConFullSig dc
                      in (dataConName dc, x, y)) dcs

toAgdaBinder :: Var -> Expr Var -> SDoc
toAgdaBinder v e = vcat
  [ ppr v <+> text ":" <+> ppVars vars <+> ppr ty
  , ppr v <+> text "="
  , nest 2 (toAgdaExpr e)
  ]
  where
    ppVars [] = empty
    ppVars vs = text "{" <+> hsep (map ppr vs) <+> text ": Set } ->"
    (vars, ty) = splitForAllTyCoVars (varType v)

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
toAgdaExpr (App e arg) = toAgdaExpr e <+> toAgdaExpr arg
toAgdaExpr (Type t) = text "{" <+> ppr t <+> text "}"
toAgdaExpr (Var v) = ppr v
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
