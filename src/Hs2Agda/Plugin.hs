{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}

module Hs2Agda.Plugin (Text, someFunc, plugin, HS2AgdaAnn(..), NI.text) where

import Hs2Agda.Plugin.CodeGen

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
import GHC (mgLookupModule, Target (targetId), ModuleGraph, TargetId (TargetModule))
import qualified Data.Set as S

someFunc :: IO ()
someFunc = putStrLn "someFunc"

data HS2AgdaAnn = HS2Agda | HS2AgdaRaw Text
  deriving (Data, Show)

getAgdaRaw :: HS2AgdaAnn -> Maybe Text
getAgdaRaw (HS2AgdaRaw x) = Just x
getAgdaRaw _ = Nothing

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

install :: CorePlugin
install _ todo = return (CoreDoPluginPass "test" pass : todo)

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
  [HS2Agda] -> Just (toAgdaBinder b e)
  _         -> Nothing
  where
    anns = lookupWithDefaultUFM_Directly env [] (varUnique b)

unpackBndr :: CoreBind -> Maybe (CoreBndr, CoreExpr)
unpackBndr = \case
  NonRec b e   -> Just (b, e)
  Rec [(b, e)] -> Just (b, e)
  _            -> Nothing

codeGenBinders :: NameEnv [HS2AgdaAnn] -> [CoreBind] -> [SDoc]
codeGenBinders env = mapMaybe (uncurry (codeGenBndr env) <=< unpackBndr)

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
