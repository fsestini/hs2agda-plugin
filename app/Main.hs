{-# OPTIONS -fplugin Hs2Agda.Plugin #-}
{-# LANGUAGE OverloadedStrings, QuasiQuotes #-}

module Main where

import Hs2Agda.Plugin

import App.Utils

data Optional a = Some a | None
{-#  ANN type Optional HS2Agda #-}

data List a = Nil | Cons a (List a)
{-#  ANN type List HS2Agda #-}

data Bogus a b = Bogus
{-#  ANN type Bogus HS2Agda #-}

{-# ANN safeHead HS2Agda #-}
safeHead :: List a -> Optional a
safeHead Nil = None
safeHead (Cons x xs) = Some x

{-# ANN listMap HS2Agda #-}
listMap :: (a -> b) -> List a -> List b
listMap f Nil = Nil
listMap f (Cons x xs) = Cons (f x) (listMap f xs)


{-# ANN module (HS2AgdaRaw [text|

safeHeadPf : forall x xs -> safeHead (Cons x xs) === Some x
safeHeadPf x xs = refl

listMapId : forall xs -> listMap (\x -> x) xs === xs
listMapId Nil = refl
listMapId (Cons x xs) rewrite listMapId xs = refl

|]) #-}


main :: IO ()
main = putStrLn "Hello, Haskell!"
