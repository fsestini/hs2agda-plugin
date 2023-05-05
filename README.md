# hs2agda-plugin

A GHC Core plugin with the aim to enable lightweight formal verification of Haskell programs by transpiling them to valid Agda code. It aims to be a dual of [agda2hs](https://github.com/agda/agda2hs).

## Usage

The idea is for the user to annotate, in the Haskell source, the definitions that they want to dump to Agda.

As the Haskell project is built and the plugin runs, it generates Agda code corresponding to the annotated definitions, writing it to files mirroring the module structure of the Haskell project.

The Agda files thus generated can then be used to prove properties about their contents.

### Example

Consider the following excerpt from the test file in `test/Hs2AgdaTest.hs`.

```haskell
{-# OPTIONS -fplugin Hs2Agda.Plugin #-}

module Main where

import Hs2Agda.Plugin

{-#  ANN type List HS2Agda #-}
data List a = Nil | Cons a (List a)

instance Functor List where
  fmap f Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)

{-# ANN listAppend HS2Agda #-}
listAppend :: List a -> List a -> List a
listAppend Nil ys = ys
listAppend (Cons x xs) ys = Cons x (listAppend xs ys)
```

Here we define, and annotate, an ADT of lists `List` and an append function `listAppend`. We also define a `Functor` instance. The `OPTION` pragma on top instructs GHC to pass the contents of this module through `Hs2Agda`, so if we run

	cabal test
	
this automatically generates a corresponding Agda module in `agda-src/Main.agda`, with the following contents:

```Agda
module Main where

open import Hs2Agda.Prelude

data List ( a : Set ) : Set where
  Nil : List a
  Cons : (a) -> (List a) -> List a

mutual
  instance
    rkP : Functor List
    rkP = MkFunctor a7PK a7Q7
  
  private
    a7Q7 : { a b : Set } -> a -> List b -> List a
    a7Q7 eta = fmap (\ ds -> eta)
    
    a7PK : { a b : Set } -> (a -> b) -> List a -> List b
    a7PK f ds_d8yi =
      case ds_d8yi of \ where
        (Nil) ->
          Nil
        (Cons x xs) ->
          Cons (f x) (fmap f xs)

listAppend : { a : Set } -> List a -> List a -> List a
listAppend ds_d8vf ys =
  case ds_d8vf of \ where
    (Nil) ->
      ys
    (Cons x xs) ->
      Cons x (listAppend xs ys)
```

While `List` and `listAppend` are quite self-explanatory and closely correspond to their Haskell counterpart, one might wonder what's the deal with `rkP`, `a7Q7`, and `a7PK`. They provide the implementation of `Functor` for `List`, where `a7Q7` and `a7PK` implement `<$` and `fmap` respectively, whereas `rkP` packages both into an instance dictionary. These bindings are automatically generated by GHC when desugaring typeclass instance definitions to Core. Because they are not user-defined, the only sensible way to refer to them is by their unique GHC-generated identifiers, hence the cryptic `rkP`, `a7Q7` and `a7PK`. Note that from a user's point of view these names don't matter, since after the typeclass instance is defined we will only ever refer to its methods via the usual dictionary accessors `fmap` etc.

#### Termination

Note that Agda performs totality-checking on definitions, thus running the module above through Agda provides (ignoring bottoms, admittedly) a lightweight proof of termination for the corresponding Haskell code.

#### Proofs

We can now use the generated Agda code to prove properties of these definitions as if we were reasoning about the corresponding Haskell code. For example, we can import the module above and prove associativity of `listAppend` and the functor laws for `List`:

```Agda
module Proofs.Main where

open import Hs2Agda.Prelude
open import Main

variable a b c : Set

append-assoc
  : (xs ys zs : List a)
  → listAppend xs (listAppend ys zs) ≡ listAppend (listAppend xs ys) zs
append-assoc Nil ys zs = refl
append-assoc (Cons x xs) ys zs = cong (Cons x) (append-assoc xs ys zs)

functor-id-law : (xs : List a) → fmap (λ x → x) xs ≡ xs
functor-id-law Nil = refl
functor-id-law (Cons x xs) = cong (Cons x) (functor-id-law xs)

functor-comp-law
  : (f : a → b) (g : b → c) (xs : List a)
  → fmap g (fmap f xs) ≡ fmap (g ∘ f) xs
functor-comp-law f g Nil = refl
functor-comp-law f g (Cons x xs) = cong (Cons _) (functor-comp-law f g xs)
```

## TODO

This project is in its early, or rather pre-natal stage. It mainly serves as a testbed for exploratory work on Haskell-to-Agda compilation, which poses several interesting challenges that I have at the moment little to no idea how to address. One example is how to deal with codata/coinduction: while Haskell does not distinguish and happily allows to mix data and codata, Agda does distinguish between the two; we thus need a way to detect instances of coinduction in Haskell code and transpile them accordingly in the corresponding Agda code, either as musical notation-style coinduction or as copatterns.

Other missing features are perhaps less conceptually interesting, and just need to be implemented. These include, but are not limited to:

- [ ] Proper control over which typeclass instances to dump to Agda.
  There is no way to annotate instances with `ANN` pragmas (and understandably so, since instances are not binders from the point of view of source Haskell). Currently, for simplicity, all instances are dumped.
- [ ] Proper handling of infix operators. I have yet to find a way to obtain fixity information for identifiers at the GHC Core level.
- [ ] Dealing with instances depending on other instances (`Functor => Applicative`, etc.)
- [ ] Proper handling of type declarations. Right now the plugin can dump simple `data`-defined ADT, but not `newtype`s or `type` synonyms.
- [ ] Handling typeclass declarations.
