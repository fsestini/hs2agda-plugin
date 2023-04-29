{-# LANGUAGE DeriveDataTypeable #-}

-- |

module Hs2Agda.Plugin.Types where

import Data.Data (Data)
import Data.Text (Text)

data HS2AgdaAnn = HS2Agda | HS2AgdaRaw Text
  deriving (Data, Show)

getAgdaRaw :: HS2AgdaAnn -> Maybe Text
getAgdaRaw (HS2AgdaRaw x) = Just x
getAgdaRaw _ = Nothing
