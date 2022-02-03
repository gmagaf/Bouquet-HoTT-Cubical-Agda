{-

This file contains:

- Proof that loopingT and windingT are group homomorphisms
- Proof that the homotopy level of the FreeGroupoid of A greater or equal of the homotopy level of ΩBouquet

-}
{-# OPTIONS --cubical #-}

module Bouquet.Bouquet.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetTruncation
open import Cubical.Algebra.Group

open import Bouquet.Bouquet.Base
open import Bouquet.Bouquet.CodeWindingLooping
open import Bouquet.Bouquet.NonTruncatedHomotopies
open import Bouquet.Bouquet.TruncatedHomotopies
open import Bouquet.FreeGroupoid
open import Bouquet.FreeGroup
open import Bouquet.FundamentalGroup

private
  variable
    ℓ : Level
    A : Type ℓ

-- loopingT and windingT are group homomorphisms

loopingTHom : GroupHom (∥freeGroupoid∥₂Group A) π₁BouquetGroup
loopingTHom = loopingT , isHom where
  isHom : IsGroupHom (∥freeGroupoid∥₂Group A .snd) loopingT (π₁BouquetGroup .snd)
  IsGroupHom.pres· isHom x y =
    elim2 (λ x y → isProp→isSet (π₁IsSet (loopingT (∣m∣₂ x y)) (∙-π₁ (loopingT x) (loopingT y)))) (λ a b → refl) x y
  IsGroupHom.pres1 isHom = refl
  IsGroupHom.presinv isHom x = elim (λ x → isProp→isSet (π₁IsSet (loopingT (∣inv∣₂ x)) (invπ₁ (loopingT x)))) (λ a → refl) x

windingTHom : GroupHom π₁BouquetGroup (∥freeGroupoid∥₂Group A)
windingTHom = windingT , isHom where
  isHom : IsGroupHom (π₁BouquetGroup .snd) windingT (∥freeGroupoid∥₂Group A .snd)
  IsGroupHom.pres· isHom x y =
    elim2 (λ x y → isProp→isSet (∥freeGroupoid∥₂IsSet (windingT (∙-π₁ x y)) (∣m∣₂ (windingT x) (windingT y)))) ind x y where
      ind : ∀ a b → windingT (∙-π₁ ∣ a ∣₂ ∣ b ∣₂) ≡ ∣m∣₂ (windingT ∣ a ∣₂) (windingT ∣ b ∣₂)
      ind a b =
        windingT (∙-π₁ ∣ a ∣₂ ∣ b ∣₂)
        ≡⟨ refl ⟩
        ∣ subst code (a ∙ b) e ∣₂
        ≡⟨ refl ⟩
        ∣ winding (a ∙ b) ∣₂
        ≡⟨ (λ i → ∣ winding ((sym (left-homotopy a) i) ∙ (sym (left-homotopy b) i)) ∣₂) ⟩
        ∣ winding ((looping (winding a)) ∙ (looping (winding b))) ∣₂
        ≡⟨ refl ⟩
        ∣ winding (looping (m (winding a) (winding b))) ∣₂
        ≡⟨ right-homotopyInTruncatedGroupoid (m (winding a) (winding b)) ⟩
        ∣ m (subst code a e) (subst code b e) ∣₂
        ≡⟨ refl ⟩
        ∣m∣₂ (windingT ∣ a ∣₂) (windingT ∣ b ∣₂) ∎
  IsGroupHom.pres1 isHom = refl
  IsGroupHom.presinv isHom x =
    elim (λ x → isProp→isSet (∥freeGroupoid∥₂IsSet (windingT (invπ₁ x)) (∣inv∣₂ (windingT x)))) ind x where
      ind : ∀ a → windingT (invπ₁ ∣ a ∣₂) ≡ ∣inv∣₂ (windingT ∣ a ∣₂)
      ind a =
        windingT (invπ₁ ∣ a ∣₂)
        ≡⟨ refl ⟩
        ∣ winding (sym a) ∣₂
        ≡⟨ (λ i → ∣ winding (sym (sym (left-homotopy a) i)) ∣₂) ⟩
        ∣ winding (sym (looping (winding a))) ∣₂
        ≡⟨ refl ⟩
        ∣ winding (looping (inv (winding a))) ∣₂
        ≡⟨ right-homotopyInTruncatedGroupoid (inv (winding a)) ⟩
        ∣ inv (winding a) ∣₂
        ≡⟨ refl ⟩
        ∣inv∣₂ (windingT ∣ a ∣₂) ∎

-- proof that the homotopy level of the FreeGroupoid of A greater or equal of the homotopy level of ΩBouquet
bouquetIsOfHLevelOfFreeGroupoid : (n : HLevel) → isOfHLevel n (FreeGroupoid A) → isOfHLevel n (ΩBouquet)
bouquetIsOfHLevelOfFreeGroupoid n freeGrpdLevel = isOfHLevelRetract n winding looping left-homotopy freeGrpdLevel
