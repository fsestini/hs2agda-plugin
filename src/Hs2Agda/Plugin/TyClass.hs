{-# LANGUAGE LambdaCase #-}

-- |

module Hs2Agda.Plugin.TyClass where

import Hs2Agda.Plugin.CodeGen

import GHC
import GHC.Plugins
import GHC.Core.InstEnv
import Data.Foldable (find)
import Data.Maybe (fromMaybe)

type VEPair = (Var, CoreExpr)

bindingPairs :: CoreBind -> (VEPair, [VEPair])
bindingPairs = \case
  NonRec b e -> ((b, e), [])
  Rec (x : xs)     -> (x, xs)

type InstanceBinders = (CoreExpr, [VEPair])

findRelated :: [CoreBind] -> Var -> (InstanceBinders, [CoreBind])
findRelated bs i = findAux bs []
  where
    findAux :: [CoreBind] -> [CoreBind] -> (InstanceBinders, [CoreBind])
    findAux [] accum = panic "could not find typeclass instance binding"
    findAux (b : bs') accum = case bindingPairs b of
      ((v, e), rest) ->
        if v == i
        then ((e, rest), []) -- TODO: filter _ accum)
        else findAux bs' (accum ++ [b])

findInstanceBinders :: Var -> [CoreBind] -> InstanceBinders
findInstanceBinders i =
  (\((_, e), rest) -> (e, rest))
  . fromMaybe (panic "could not find typeclass instance binding")
  . find ((== i) . fst . fst) . map bindingPairs

ppInstanceBinders :: Var -> InstanceBinders -> SDoc
ppInstanceBinders dictFun (e, bs) =
  if null bs then block else vcat [ text "mutual", nest 2 block ]
  where
    block = vcat $
      [ text "instance" -- <+> ppAgdaDecl dictFun
      --, ppAgdaTopLevel dictFun empty e
      , nest 2 (ppAgdaTopLevel dictFun e)
      ] ++
      map (uncurry ppAgdaTopLevel) bs

ppAgdaTyClassInst :: [CoreBind] -> ClsInst -> SDoc
ppAgdaTyClassInst bs i = -- pprInstance i <+> ppr (is_dfun i) <+> ppr (is_dfun i)
  vcat
    [ ppr (map (\x -> let nm = varName x ; onm = getOccName x in
                  [ ppr (idName x)
                  , ppr (isGlobalId x)
                  , ppr (isDerivedOccName onm) -- TODO: use this to filter
                  , ppr (isDefaultMethodOcc onm)
                  ]) fvs)
    , ppr (localiseId dictFun)
    , ppr (map splitAppTys (is_tys i))
    , ppInstanceBinders dictFun (e, bs')
    ]
  -- [ text "instance" <+> ppAgdaDecl dictFun
  -- , ppAgdaTopLevel dictFun empty e
  -- , fvs
  -- ]
  -- [ ppr vs
  -- , ppr tys
  -- , ppr c
  -- , ppr tys'
  -- ]
  where
    dictFun = is_dfun i
    dictTy = hcatsp $
      let x = [ppr c, parens (ppr (head tys'))]
      in if null vs
         then x
         else  (text "forall" : map ppTyBndr vs) ++ (text "->" : x)
    (e, bs') = findInstanceBinders dictFun bs
    fvs = filter (`notElem` (dictFun : map fst bs'))
           -- (pAnd (`notElem` (dictFun : map fst bs')) (isDerivedOccName . occName))
        . concatMap (dVarSetElems . freeVarsOf . freeVars)
        $ (e : map snd bs')
    -- ((e, bs'), _) = findRelated bs dictFun
    -- bodies = vcat (map (uncurry toAgdaTopLevel) ((dictFun, e) : bs'))


      -- ppr [ppr vs, ppr tys, ppr c, ppr tys']
    -- (vs, c, tys) = instanceHead i
    (vs, tys, c, tys') = instanceSig i

-- allVars :: CoreExpr -> [Var]
-- allVars = undefined

-- freeVars :: [VEPair] -> [Var]
-- freeVars bs = filter (`notElem` boundVs) vs
--   where
--     vs = concatMap allVars (concatMap rhssOfBind bs)
--     boundVs = bindersOfBinds bs

-- freeVarsOfVEPairs :: [VEPair] -> SDoc
-- freeVarsOfVEPairs = ppr . map (freeVars . snd)

pAnd :: (a -> Bool) -> (a -> Bool) -> a -> Bool
pAnd f g x = f x && g x
