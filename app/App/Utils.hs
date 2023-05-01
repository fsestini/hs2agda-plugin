{-# OPTIONS -fplugin Hs2Agda.Plugin #-}

module App.Utils where

import Hs2Agda.Plugin

{-# ANN type Reader HS2Agda #-}
data Reader r a = MkReader (r -> a)

instance Functor (Reader r) where
  fmap f (MkReader h) = MkReader (\r -> f (h r))

{-# ANN doubleMap HS2Agda #-}
doubleMap :: (a -> b) -> (b -> c) -> Reader r a -> Reader r c
doubleMap f g re = fmap g (fmap f re)

-- {-# ANN bindReader HS2Agda #-}
-- bindReader :: Reader r a -> (a -> Reader r b) -> Reader r b
-- bindReader (MkReader f) h =
--   MkReader (\r ->
--     case h (f r) of
--       (MkReader g) -> g r)
