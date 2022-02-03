{-

This file contains:

- Definition of the Bouquet of circles of a type aka wedge of A circles

-}
{-# OPTIONS --cubical #-}

module Bouquet.Bouquet.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level

data Bouquet (A : Type ℓ) : Type ℓ where
  base : Bouquet A
  loop : A → base ≡ base
