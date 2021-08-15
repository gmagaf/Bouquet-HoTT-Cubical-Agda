{-

This file contains:

- Definition of truncated encode decode functions
- Proof of the truncated versions of decodeEncode and encodeDecode
- Proof that π₁WA ≡ FreeGroup A

-}
{-# OPTIONS --cubical #-}

module WA.WA.TruncatedHomotopies where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.SetTruncation renaming (rec to recTrunc)


open import WA.WA.Base
open import WA.WA.CodeWindingLooping
open import WA.WA.NonTruncatedHomotopies
open import WA.FreeGroupoid
open import WA.FreeGroup
open import WA.FundamentalGroup

encodeT : ∀ {ℓ}{A : Type ℓ} → (x : W A) → ∥ base ≡ x ∥₂ → ∥ code x ∥₂
encodeT x = map (encode x)

decodeT : ∀ {ℓ}{A : Type ℓ} → (x : W A) → ∥ code x ∥₂ → ∥ base ≡ x ∥₂
decodeT x = map (decode x)

decodeEncodeT : ∀ {ℓ}{A : Type ℓ} → (x : W A) → (p : ∥ base ≡ x ∥₂) → decodeT x (encodeT x p) ≡ p
decodeEncodeT x g = elim sethood induction g where
  sethood : (q : ∥ base ≡ x ∥₂) → isSet (decodeT x (encodeT x q) ≡ q)
  sethood q = isProp→isSet (squash₂ (decodeT x (encodeT x q)) q)
  induction : (l : base ≡ x) → ∣ decode x (encode x l) ∣₂ ≡ ∣ l ∣₂
  induction l = cong (λ l' → ∣ l' ∣₂) (decodeEncode x l)

encodeDecodeT : ∀ {ℓ}{A : Type ℓ} → (x : W A) → (g : ∥ code x ∥₂) → encodeT x (decodeT x g) ≡ g
encodeDecodeT x g = elim sethood induction g where
  sethood : (z : ∥ code x ∥₂) → isSet (encodeT x (decodeT x z) ≡ z)
  sethood z = isProp→isSet (squash₂ (encodeT x (decodeT x z)) z)
  induction : (a : code x) → ∣ encode x (decode x a) ∣₂ ≡ ∣ a ∣₂
  induction a = encodeDecodeInTruncatedGroupoid x a

TruncatedFamiliesIso : ∀ {ℓ}{A : Type ℓ} → (x : W A) → Iso ∥ base ≡ x ∥₂ ∥ code x ∥₂
Iso.fun (TruncatedFamiliesIso x)      = encodeT x
Iso.inv (TruncatedFamiliesIso x)      = decodeT x
Iso.rightInv (TruncatedFamiliesIso x) = encodeDecodeT x
Iso.leftInv (TruncatedFamiliesIso x)  = decodeEncodeT x

TruncatedFamiliesEquiv : ∀ {ℓ}{A : Type ℓ} → (x : W A) → ∥ base ≡ x ∥₂ ≃ ∥ code x ∥₂
TruncatedFamiliesEquiv x = isoToEquiv (TruncatedFamiliesIso x)

TruncatedFamilies≡ : ∀ {ℓ}{A : Type ℓ} → (x : W A) → ∥ base ≡ x ∥₂ ≡ ∥ code x ∥₂
TruncatedFamilies≡ x = ua (TruncatedFamiliesEquiv x)

π₁WA≡∥FreeGroupoid∥₂ : ∀ {ℓ}{A : Type ℓ} → π₁WA ≡ ∥ FreeGroupoid A ∥₂
π₁WA≡∥FreeGroupoid∥₂ = TruncatedFamilies≡ base

π₁WA≡FreeGroup : ∀ {ℓ}{A : Type ℓ} → π₁WA ≡ FreeGroup A
π₁WA≡FreeGroup {A = A} =
  π₁WA
  ≡⟨ π₁WA≡∥FreeGroupoid∥₂ ⟩
  ∥ FreeGroupoid A ∥₂
  ≡⟨ sym freeGroupTruncIdempotent ⟩
  FreeGroup A ∎
