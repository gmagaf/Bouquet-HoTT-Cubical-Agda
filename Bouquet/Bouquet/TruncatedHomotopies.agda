{-

This file contains:

- Definition of truncated encode decode functions
- Proof of the truncated versions of decodeEncode and encodeDecode
- Proof that π₁Bouquet ≡ FreeGroup A

-}
{-# OPTIONS --cubical #-}

module Bouquet.Bouquet.TruncatedHomotopies where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.SetTruncation renaming (rec to recTrunc)


open import Bouquet.Bouquet.Base
open import Bouquet.Bouquet.CodeWindingLooping
open import Bouquet.Bouquet.NonTruncatedHomotopies
open import Bouquet.FreeGroupoid
open import Bouquet.FreeGroup
open import Bouquet.FundamentalGroup

private
  variable
    ℓ : Level
    A : Type ℓ


encodeT : (x : Bouquet A) → ∥ base ≡ x ∥₂ → ∥ code x ∥₂
encodeT x = map (encode x)

decodeT : (x : Bouquet A) → ∥ code x ∥₂ → ∥ base ≡ x ∥₂
decodeT x = map (decode x)

decodeEncodeT : (x : Bouquet A) → (p : ∥ base ≡ x ∥₂) → decodeT x (encodeT x p) ≡ p
decodeEncodeT x g = elim sethood induction g where
  sethood : (q : ∥ base ≡ x ∥₂) → isSet (decodeT x (encodeT x q) ≡ q)
  sethood q = isProp→isSet (squash₂ (decodeT x (encodeT x q)) q)
  induction : (l : base ≡ x) → ∣ decode x (encode x l) ∣₂ ≡ ∣ l ∣₂
  induction l = cong (λ l' → ∣ l' ∣₂) (decodeEncode x l)

encodeDecodeT : (x : Bouquet A) → (g : ∥ code x ∥₂) → encodeT x (decodeT x g) ≡ g
encodeDecodeT x g = elim sethood induction g where
  sethood : (z : ∥ code x ∥₂) → isSet (encodeT x (decodeT x z) ≡ z)
  sethood z = isProp→isSet (squash₂ (encodeT x (decodeT x z)) z)
  induction : (a : code x) → ∣ encode x (decode x a) ∣₂ ≡ ∣ a ∣₂
  induction a = encodeDecodeInTruncatedGroupoid x a

TruncatedFamiliesIso : (x : Bouquet A) → Iso ∥ base ≡ x ∥₂ ∥ code x ∥₂
Iso.fun (TruncatedFamiliesIso x)      = encodeT x
Iso.inv (TruncatedFamiliesIso x)      = decodeT x
Iso.rightInv (TruncatedFamiliesIso x) = encodeDecodeT x
Iso.leftInv (TruncatedFamiliesIso x)  = decodeEncodeT x

TruncatedFamiliesEquiv : (x : Bouquet A) → ∥ base ≡ x ∥₂ ≃ ∥ code x ∥₂
TruncatedFamiliesEquiv x = isoToEquiv (TruncatedFamiliesIso x)

TruncatedFamilies≡ : (x : Bouquet A) → ∥ base ≡ x ∥₂ ≡ ∥ code x ∥₂
TruncatedFamilies≡ x = ua (TruncatedFamiliesEquiv x)

π₁Bouquet≡∥FreeGroupoid∥₂ : π₁Bouquet ≡ ∥ FreeGroupoid A ∥₂
π₁Bouquet≡∥FreeGroupoid∥₂ = TruncatedFamilies≡ base

π₁Bouquet≡FreeGroup : {A : Type ℓ} → π₁Bouquet ≡ FreeGroup A
π₁Bouquet≡FreeGroup {A = A} =
  π₁Bouquet
  ≡⟨ π₁Bouquet≡∥FreeGroupoid∥₂ ⟩
  ∥ FreeGroupoid A ∥₂
  ≡⟨ sym freeGroupTruncIdempotent ⟩
  FreeGroup A ∎
