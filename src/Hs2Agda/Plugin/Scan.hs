{-# LANGUAGE LambdaCase #-}

-- |

module Hs2Agda.Plugin.Scan
  ( getTargetedImports
  , getActiveTyCons
  , toUnifiedBind
  , ActiveBind(..)
  , ScanEnv(..)
  , ScanError(..)
  , CoreBEPair
  , UnifiedBind
  , NonEmpty(..)
  , scanBinds
  , ppScanError
  )
  where

import GHC
import GHC.Plugins
import qualified Data.Set as S
import Data.Maybe (mapMaybe, fromMaybe)
import Data.List.NonEmpty as NE (NonEmpty (..), singleton)
import Hs2Agda.Plugin.Types (HS2AgdaAnn)
import qualified Data.Foldable as NE
import Data.Bool (bool)
import Data.Either (partitionEithers)
import GHC.Core.InstEnv (ClsInst(..))
import Data.List (find, intersperse)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans
import Data.Tuple.Extra ((***))

getTargetedImports :: HscEnv -> Module -> [ModuleName]
getTargetedImports henv m = localImports
  where
    modGraph     = hsc_mod_graph henv
    targets      = hsc_targets henv
    modTargets   = mapMaybe targetModule targets
    localImports = filter (`elem` modTargets) allImports
    allImports   =
      maybe (panic "module is not in module graph")
            (map (unLoc . snd) . ms_textual_imps)
            (mgLookupModule modGraph m)
    targetModule :: Target -> Maybe ModuleName
    targetModule t = case targetId t of
      TargetModule m -> Just m
      _              -> Nothing

getActiveTyCons :: NameEnv [HS2AgdaAnn] -> [TyCon] -> [TyCon]
getActiveTyCons env = filter (flip elemNameEnv env .tyConName)

type CoreBEPair = (CoreBndr, CoreExpr)
type UnifiedBind = NonEmpty CoreBEPair

toUnifiedBind :: CoreBind -> UnifiedBind
toUnifiedBind (NonRec b e) = (b, e) :| []
toUnifiedBind (Rec ((b,e):xs)) = (b,e) :| xs

ubBinders :: UnifiedBind -> [CoreBndr]
ubBinders = map fst . NE.toList

data ActiveBind
  = Annotated UnifiedBind
  | Instance [UnifiedBind] UnifiedBind

newtype Miss a = Miss a
newtype Hit a = Hit a

data ScanError
  = RecAnnE (Miss [Name]) (Hit [Name])
  | InstanceE [Name] ClsInst

data ScanEnv = ScanEnv
  { annNameEnv :: NameEnv [HS2AgdaAnn]
  , localInsts :: [ClsInst]
  }

data ScanState = ScanState
  { activeBinds    :: [ActiveBind]
  , auxiliaryBinds :: [CoreBEPair]
  }

initialScanState :: ScanState
initialScanState = ScanState [] []

type S = ReaderT ScanEnv (StateT ScanState (Either ScanError))

addAux :: CoreBEPair -> S ()
addAux p = lift (modify (\st -> st { auxiliaryBinds = p : auxiliaryBinds st }))

addActive :: ActiveBind -> S ()
addActive a = lift (modify (\st -> st { activeBinds = a : activeBinds st }))

checkAnnsS :: [Name] -> S (Miss [Name], Hit [Name])
checkAnnsS nms = flip checkAnns nms . annNameEnv <$> ask
  where
    isAnnotated :: NameEnv [HS2AgdaAnn] -> Name -> Bool
    isAnnotated env = not . null . lookupWithDefaultUFM_Directly env [] . nameUnique
    checkAnns :: NameEnv [HS2AgdaAnn] -> [Name] -> (Miss [Name], Hit [Name])
    checkAnns env =
      (Miss *** Hit) . partitionEithers .
      map (\b -> bool (Left b) (Right b) (isAnnotated env b))

findAuxiliaryBinds :: [Name] -> S [CoreBEPair]
findAuxiliaryBinds nms = do
  res <- reverse . filter ((`elem` nms) . varName . fst) . auxiliaryBinds <$> lift get
  if length res == length nms
    then pure res
    else panic "could not find required auxiliary binding"

guardExcept :: Bool -> ScanError -> S ()
guardExcept b e = if b then pure () else throwS e

throwS :: ScanError -> S ()
throwS = lift . lift . Left

getClsInst :: DFunId -> S ClsInst
getClsInst f =
  fromMaybe (panic "could not find ClsInst")
  . find ((== f) . is_dfun) . localInsts
  <$> ask

-- | Analyze dictionary function binding (i.e. a typeclass instance),
-- and possibly add it to the list of bindings to emit to the Agda module.
--
-- Currently we just accept all such bindings as long as their code can be
-- safely emitted, that is, as long as all free variables in the
-- body of the instance methods have been user-annotated, which means they
-- will end up in the Agda code.
scanDFun :: UnifiedBind -> S ()
scanDFun x@((b,e) :| ubs) = do
  i <- getClsInst b
  (Miss xs, _) <- checkAnnsS (map varName fvs)
  let fvsNotDerived = filter (not . isDerivedOccName . occName) xs
  guardExcept (null fvsNotDerived) (InstanceE fvsNotDerived i)
  auxs <- findAuxiliaryBinds xs -- traverse findAuxiliaryBind xs
  addActive (Instance (map NE.singleton auxs) x)
  where
    rhss = e : map snd ubs
    fvs = filter (`notElem` (b : map fst ubs)) . concatMap exprFreeVarsList $ rhss

scanBind :: UnifiedBind -> S ()
scanBind x@((b,e) :| ubs)
  | isDFunId b
    = scanDFun x
  | isDerivedOccName (occName b)
    = if null ubs then addAux (b,e) else panic "found recursive auxiliary binding"
  | otherwise
    = do checkAnnsS (map varName (ubBinders x)) >>= \case
           -- all bindings are annotated (no misses)
           (Miss [], _) -> addActive (Annotated x)
           -- no bindings are annotated (we do nothing)
           (_, Hit [])  -> pure ()
           -- some bindings are annotated, some not
           (x,y)        -> throwS (RecAnnE x y)

-- | Traverse a list of Core top-level bindings to retrieve which of them should be
-- emitted to the Agda file for the current module.
--
-- In particular, we emit:
-- * All bindings that have an associated user-defined ANN pragma.
-- * All bindings corresponding to typeclass instance dictionary definitions.
scanBinds :: ScanEnv -> [UnifiedBind] -> Either ScanError [ActiveBind]
scanBinds env =
  fmap (reverse . activeBinds . snd)
  . runS env initialScanState . traverse scanBind
  where runS e s x = runStateT (runReaderT x e) s

ppScanError :: ScanError -> SDoc
ppScanError = \case
  RecAnnE (Miss xs) (Hit ys) -> vcat $
    [ text "annotated bindings"
    , nest 2 (hcat (intersperse (text ",") (map ppr ys)))
    , text "are mutually defined with bindings"
    , nest 2 (hcat (intersperse (text ",") (map ppr xs)))
    , text "which are not annotated"
    ]
  InstanceE nms cls -> vcat $
    [ text "typeclass instance declaration"
    , nest 2 (ppr cls)
    , text "requires the bindings"
    , nest 2 (hcat (intersperse (text ",") (map ppr nms)))
    , text "which are not annotated"
    ]
