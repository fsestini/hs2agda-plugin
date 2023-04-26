{-# OPTIONS -fplugin Hs2Agda.Plugin #-}

module App.Utils where

import Hs2Agda.Plugin

{-# ANN type Reader HS2Agda #-}
data Reader r a = Reader (r -> a)

{-# ANN bindReader HS2Agda #-}
bindReader :: Reader r a -> (a -> Reader r b) -> Reader r b
bindReader (Reader f) h =
  Reader (\r ->
    case h (f r) of
      (Reader g) -> g r)
