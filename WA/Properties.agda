{-

This file contains:

- Proof that loopingT and windingT are group homomorphisms
- Examples

-}
{-# OPTIONS --cubical #-}

module WA.WA.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Univalence
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Path
-- open import Cubical.HITs.PropositionalTruncation renaming (rec to propRec)
open import Cubical.HITs.SetTruncation
-- open import Cubical.HITs.GroupoidTruncation
-- open import Cubical.Data.Unit
-- open import Cubical.Data.Empty
-- open import Cubical.Data.Int
open import Cubical.Algebra.Group

open import WA.WA.Base
open import WA.WA.CodeWindingLooping
open import WA.WA.NonTruncatedHomotopies
open import WA.WA.TruncatedHomotopies
open import WA.FreeGroupoid
open import WA.FreeGroup
open import WA.FundamentalGroup

-- loopingT and windingT are group homomorphisms

loopingTHom : ∀ {ℓ}{A : Type ℓ} → GroupHom (∥freeGroupoid∥₂Group A) π₁WAGroup
loopingTHom {A = A} = loopingT , isHom where
  isHom : IsGroupHom (∥freeGroupoid∥₂Group A .snd) loopingT (π₁WAGroup .snd)
  IsGroupHom.pres· isHom x y =
    elim2 (λ x y → isProp→isSet (π₁IsSet (loopingT (∣m∣₂ x y)) (∙-π₁ (loopingT x) (loopingT y)))) (λ a b → refl) x y
  IsGroupHom.pres1 isHom = refl
  IsGroupHom.presinv isHom x = elim (λ x → isProp→isSet (π₁IsSet (loopingT (∣inv∣₂ x)) (invπ₁ (loopingT x)))) (λ a → refl) x

windingTHom : ∀ {ℓ}{A : Type ℓ} → GroupHom π₁WAGroup (∥freeGroupoid∥₂Group A)
windingTHom {A = A} = windingT , isHom where
  isHom : IsGroupHom (π₁WAGroup .snd) windingT (∥freeGroupoid∥₂Group A .snd)
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



-- WAisOfHLevelOfFreeGroupoid : ∀ {ℓ}{A : Type ℓ} → (n : HLevel) → isOfHLevel n (FreeGroupoid A) → isOfHLevel n (ΩWA)
-- WAisOfHLevelOfFreeGroupoid n freeGrpdLevel = isOfHLevelRetract n winding looping left-homotopy freeGrpdLevel
--
-- FreeGroupoidisOfHLevelOfWA : ∀ {ℓ}{A : Type ℓ} → (n : HLevel) → isOfHLevel n (ΩWA) → isOfHLevel n (FreeGroupoid A)
-- FreeGroupoidisOfHLevelOfWA n waLevel = propRec (isPropIsOfHLevel n) baseStep truncatedRetract where
--   baseStep : (∀ g → winding (looping g) ≡ g) → isOfHLevel n _
--   baseStep retract = isOfHLevelRetract n looping winding retract waLevel
--   postulate truncatedRetract : ∥ (∀ g → winding (looping g) ≡ g) ∥
--   -- truncatedRetract = propRec squash {!   !} {!   !}
--
-- -- ex 1: circle
--
-- Z = FreeGroupoid Unit
--
-- postulate idempotentZ : Z ≡ ℤ
-- -- idempotentZ = ua (isoToEquiv isoZ) where
-- --   fun : Z → ℤ
-- --   fun (η tt) = 1
-- --   fun (m g1 g2) = (fun g1) + (fun g2)
-- --   fun e = 0
-- --   fun (inv g) = - (fun g)
-- --
-- --   isoZ : Iso Z ℤ
-- --   Iso.fun isoZ      = {!   !}
-- --   Iso.inv isoZ      = {!   !}
-- --   Iso.rightInv isoZ = {!   !}
-- --   Iso.leftInv isoZ  = {!   !}
--
-- isSetZ : isSet Z
-- isSetZ = subst isSet (sym idempotentZ) isSetℤ
--
-- isSetΩWUnit : isSet (ΩWA {A = Unit})
-- isSetΩWUnit = WAisOfHLevelOfFreeGroupoid 2 isSetZ
--
-- isGroupoidWUnit : isGroupoid (W Unit)
-- isGroupoidWUnit = ind where
--   ind : ∀ x y → isSet (x ≡ y)
--   ind base base               = isSetΩWUnit
--   ind (loop tt i) base        = isProp→PathP (λ i → isPropIsSet {A = (loop tt i) ≡ base}) isSetΩWUnit isSetΩWUnit i
--   ind base (loop tt i)        = isProp→PathP (λ i → isPropIsSet {A = base ≡ (loop tt i)}) isSetΩWUnit isSetΩWUnit i
--   ind (loop tt i) (loop tt j) = isProp→SquareP (λ i j → isPropIsSet {A = (loop tt i) ≡ (loop tt j)})
--                                   (λ i → ind (loop tt i) base) (λ i → ind (loop tt i) base)
--                                   (λ i → ind base (loop tt i)) (λ i → ind base (loop tt i)) i j
--
--
-- postulate isNotSetZ : isSet Z → ⊥
--
--
-- -- ex 2: empty group
--
-- Empty = FreeGroupoid ⊥
--
--
-- postulate groupoidEq : ∀ {ℓ}{A : Type ℓ} → ∥ ΩWA {A = A} ∥₃ ≡ ∥ FreeGroupoid A ∥₃
--
-- π₂WA : ∀ {ℓ}{A : Type ℓ} → Type ℓ
-- π₂WA {A = A} = ∥ refl {x = base {A = A}} ≡ refl ∥₂  --∥ Ω {A = ΩWA {A = A}} {base = refl} ∥₂
--
-- pathEq : ∀ {ℓ}{A : Type ℓ} → Iso (∣ refl {x = base {A = A}} ∣₃ ≡ ∣ refl ∣₃) (π₂WA {A = A})
-- Iso.fun pathEq      = {!   !}
-- Iso.inv pathEq      = {!   !}
-- Iso.rightInv pathEq = {!   !}
-- Iso.leftInv pathEq  = {!   !}
--
-- postulate typesEq : ∀ {ℓ}{A : Type ℓ} → (∣ e {A = A} ∣₃ ≡ ∣ e ∣₃) ≡ π₂WA {A = A}
