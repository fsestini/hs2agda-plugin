{-# OPTIONS -fplugin Hs2Agda.Plugin #-}
{-# LANGUAGE OverloadedStrings, QuasiQuotes #-}

module Main where

import Hs2Agda.Plugin

import App.Utils

main :: IO ()
main = putStrLn "Hello, Haskell!"

data Optional a = Some a | None
{-#  ANN type Optional HS2Agda #-}

data List a = Nil | Cons a (List a)
{-#  ANN type List HS2Agda #-}

data Bogus a b = MkBogus
{-#  ANN type Bogus HS2Agda #-}

instance Functor List where
  fmap f Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)

instance Functor (Bogus a) where
  fmap _ MkBogus = MkBogus

{-}
{-# ANN safeHead HS2Agda #-}
safeHead :: List a -> Optional a
safeHead Nil = None
safeHead (Cons x xs) = Some x

{-# ANN listMap HS2Agda #-}
listMap :: (a -> b) -> List a -> List b
listMap f Nil = Nil
listMap f (Cons x xs) = Cons (f x) (listMap f xs)

{-# ANN append HS2Agda #-}
append :: List a -> List a -> List a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

{-# ANN singleton HS2Agda #-}
singleton :: a -> List a
singleton x = Cons x Nil

{-# ANN rev HS2Agda #-}
rev :: List a -> List a -> List a
rev Nil ys = ys
rev (Cons x xs) ys = rev xs (Cons x ys)

{-# ANN fastRev HS2Agda #-}
fastRev :: List a -> List a
fastRev xs = rev xs Nil

reverse :: List a -> List a
reverse Nil = Nil
reverse (Cons x xs) = append (Main.reverse xs) (singleton x)

{-# ANN module (HS2AgdaRaw [text|

safeHeadPf : forall {a} x (xs : List a) -> safeHead (Cons x xs) === Some x
safeHeadPf x xs = refl

listMapId : forall {a} (xs : List a) -> listMap (\x -> x) xs === xs
listMapId Nil = refl
listMapId (Cons x xs) rewrite listMapId xs = refl

rev-lemma : forall {a} (xs : List a) -> reverse xs === fastRev xs
rev-lemma Nil = refl
rev-lemma (Cons x xs) = {!!}

|]) #-}

-}
