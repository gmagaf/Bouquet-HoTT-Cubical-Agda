{-

This file contains:

- Definition of the wedge of A circles of a type aka bouquet

-}
{-# OPTIONS --cubical #-}

module WA.WA.Base where

open import Cubical.Foundations.Prelude

data W {ℓ}(A : Type ℓ) : Type ℓ where
  base : W A
  loop : A → base ≡ base
