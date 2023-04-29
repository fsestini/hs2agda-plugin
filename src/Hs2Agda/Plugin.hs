module Hs2Agda.Plugin (Text, someFunc, plugin, HS2AgdaAnn(..), NI.text) where

import Hs2Agda.Plugin.CodeGen
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
import Data.List.Split (splitOn)
import System.FilePath ((</>), takeDirectory)
import GHC (mgLookupModule, Target (targetId), ModuleGraph, TargetId (TargetModule), ClsInst)
import qualified Data.Set as S
import Hs2Agda.Plugin.TyClass (ppAgdaTyClassInst)

someFunc :: IO ()
someFunc = putStrLn "someFunc"

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

install :: CorePlugin
install _ todo = return (CoreDoPluginPass "test" pass : todo)

getImportedModules :: ModuleGraph -> Module -> [Located ModuleName]
getImportedModules modGraph m =
  maybe (panic "module is not in module graph")
        (map snd . ms_textual_imps)
        (mgLookupModule modGraph m)

getTargetedImports :: [Target] -> [Located ModuleName] -> [ModuleName]
getTargetedImports ts ls = S.toList (S.intersection targets imports)
  where
    targets = S.fromList (mapMaybe targetModule ts)
    imports = S.fromList (map unLoc ls)
    targetModule :: Target -> Maybe ModuleName
    targetModule t = case targetId t of
      TargetModule m -> Just m
      _              -> Nothing

pass :: ModGuts -> CoreM ModGuts
pass g = do
  m <- getModule
  dflags <- getDynFlags
  henv <- getHscEnv

  let allImports   = getImportedModules (hsc_mod_graph henv) m
      localImports = getTargetedImports (hsc_targets henv) allImports
  putMsg (ppr localImports)
  --  putMsg (ppr mtargs)

  putMsg (text "We are in module:" <+> pprModule m)

  putMsgS "Instances:"
  forM_ (mg_insts g) (putMsg . ppAgdaTyClassInst (mg_binds g))
  -- putMsg (ppr (map (ppAgdaTyClassInst (mg_binds g)) (mg_insts g)))

  -- putMsgS "Binders:"
  -- putMsg (ppr (mg_binds g))
  -- putMsg . ppr . map (ppr . map (\b -> ppr (varUnique b) <+> text "::" <+> ppr (varType b))) .
  --   flip map (mg_binds g) $ \case
  --     (NonRec b _) -> [b] -- ppr b <+> ppr (varType b)
  --     Rec bs -> map fst bs

  (xx, yy) <- getAnnotations deserializeWithData g
  let cgres = codeGenAnns xx yy (mg_tcs g) (mg_binds g)

  let wholeMod = ppWholeModule (moduleName m) localImports cgres
  putMsg wholeMod

  let agdaFilePath = (mkAgdaFilePath . agdaModulePath) (moduleName m)
  putMsgS $ "Writing file: " ++ agdaFilePath
  liftIO $ do
    createDirectoryIfMissing True (takeDirectory agdaFilePath)
    writeFile agdaFilePath (showSDoc dflags wholeMod)

  return g

mkAgdaFilePath :: ([String], String) -> FilePath
mkAgdaFilePath (xs, x) = foldr (</>) (x ++ ".agda") ("agda-src" : xs)

agdaModulePath :: ModuleName -> ([String], String)
agdaModulePath m =
  if null x then ([], s) else (take (length x - 1) x, last x)
  where
    s = moduleNameString m
    x = splitOn "." s

-- printAnn' :: DynFlags -> ModGuts -> CoreBndr -> CoreExpr -> CoreM ()
-- printAnn' dflags guts b e = do
--   anns <- annotationsOn guts b :: CoreM [HS2AgdaAnn]
--   unless (null anns) $ do
--     putMsgS $ "Annotated binding found: " ++  showSDoc dflags (ppr b)
--     putMsgS (show anns)
--     case anns of
--       [HS2AgdaRaw s] -> putMsgS (unpack s)
--       _              -> putMsg $ toAgdaBinder b e

-- printAnn :: DynFlags -> ModGuts -> CoreBind -> CoreM ()
-- printAnn dflags guts bndr@(NonRec b e) = printAnn' dflags guts b e
-- printAnn dflags guts bndr@(Rec [(b, e)]) = printAnn' dflags guts b e
-- printAnn _ _ bndr = return ()

-- annotationsOn :: Data a => ModGuts -> CoreBndr -> CoreM [a]
-- annotationsOn guts bndr = do
--   (_, anns) <- getAnnotations deserializeWithData guts
--   return $ lookupWithDefaultUFM_Directly anns [] (varUnique bndr)
