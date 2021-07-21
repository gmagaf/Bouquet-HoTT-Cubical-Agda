{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv


open import WA.WA
open import WA.FreeGroupoid
open import WA.GroupoidIsomorphisms
open import WA.Code_Winding

module WA.LeftHomotopy where

-- left-homotopy : ∀ {ℓ}{A : Type ℓ} → ∀ (l : base ≡ base) → looping (winding l) ≡ l
