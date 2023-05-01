{-# OPTIONS -fplugin Hs2Agda.Plugin #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Hs2Agda.Plugin

main :: IO ()
main = putStrLn "Hello Hs2Agda"

data Optional a = Some a | None
{-#  ANN type Optional HS2Agda #-}

data List a = Nil | Cons a (List a)
{-#  ANN type List HS2Agda #-}

instance Functor List where
  fmap f Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)

{-# ANN safeHead HS2Agda #-}
safeHead :: List a -> Optional a
safeHead = \case
  Nil -> None
  (Cons x xs) -> Some x

{-# ANN listAppend HS2Agda #-}
listAppend :: List a -> List a -> List a
listAppend Nil ys = ys
listAppend (Cons x xs) ys = Cons x (listAppend xs ys)
