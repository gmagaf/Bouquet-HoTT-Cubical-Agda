{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

module WA.WA where

private
  variable
    ℓ : Level

data W (A : Type ℓ) : Type ℓ where
  base : W A
  loop : A → base ≡ base
