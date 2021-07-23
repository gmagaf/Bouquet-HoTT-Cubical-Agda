{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv


open import WA.WA
open import WA.FreeGroup
open import WA.GroupoidIsomorphisms
open import WA.CodeWindingLooping

module WA.LeftHomotopy where

-- left-homotopy : ∀ {ℓ}{A : Type ℓ} → ∀ (r : π₁WA {A = A}) → looping (winding r) ≡ r
