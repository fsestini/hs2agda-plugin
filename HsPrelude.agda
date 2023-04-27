module HsPrelude where

open import Relation.Binary.PropositionalEquality public

case_of_ : {a b : Set} → a → (a → b) → b
case_of_ x f = f x
{-# INLINE case_of_ #-}

_===_ = _≡_
