{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)
open import Cubical.HITs.SetTruncation

open import WA.WA
open import WA.FreeGroup
open import WA.GroupoidIsomorphisms
open import WA.CodeWindingLooping
open import WA.FundamentalGroup

module WA.RightHomotopy where


η-right-homotopy : ∀ {ℓ}{A : Type ℓ} → ∀ (a : A) → winding (looping (η a)) ≡ η a
η-right-homotopy a =
  winding (looping (η a))
  ≡⟨ refl ⟩
  rec freeGroupIsSet (λ l → transport (cong code l) e) ∣ loop a ∣₂
  ≡⟨ refl ⟩
  transport (cong code (loop a)) e
  ≡⟨ refl ⟩
  transport (pathsInU (η a)) e
  ≡⟨ uaβ (equivs (η a)) e ⟩
  m(e , η a)
  ≡⟨ sym (idl (η a)) ⟩
  η a ∎

-- right-homotopy : ∀ {ℓ}{A : Type ℓ} → ∀ (g : FreeGroupoid A) → winding (looping g) ≡ g
