{-

This file contains:

- Definitions of the loop space and fundamental group of a type

-}
{-# OPTIONS --cubical #-}

module Bouquet.FundamentalGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetTruncation

private
  variable
    ℓ : Level

Ω : {A : Type ℓ}{base : A} → Type ℓ
Ω {base = base} = base ≡ base

π₁ : {A : Type ℓ}{base : A} → Type ℓ
π₁ {base = base} = ∥ Ω {base = base} ∥₂
