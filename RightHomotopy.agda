{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Algebra.Group

open import WA.WA
open import WA.FreeGroup
open import WA.GroupIsomorphisms
open import WA.CodeWindingLooping
open import WA.FundamentalGroup

module WA.RightHomotopy where

Bprop : ∀ {ℓ}{A : Type ℓ} → (g : FreeGroup A) → isProp (winding (looping g) ≡ g)
Bprop g = freeGroupIsSet (winding (looping g)) g

η-ind : ∀ {ℓ}{A : Type ℓ} → (a : A) → winding (looping (η a)) ≡ η a
η-ind a =
  winding (looping (η a))
  ≡⟨ refl ⟩
  subst code (loop a) e
  ≡⟨ refl ⟩
  transport (cong code (loop a)) e
  ≡⟨ refl ⟩
  transport (ua (equivs (η a))) e
  ≡⟨ uaβ (equivs (η a)) e ⟩
  m e (η a)
  ≡⟨ sym (idl (η a)) ⟩
  η a ∎

m-ind : ∀{ℓ}{A : Type ℓ} → (g1 g2 : FreeGroup A) → winding (looping g1) ≡ g1 → winding (looping g2) ≡ g2 →
  winding (looping (m g1 g2)) ≡ (m g1 g2)
m-ind g1 g2 ind1 ind2 =
  winding (looping (m g1 g2))
  ≡⟨ cong winding (IsGroupHom.pres· (loopingHom .snd) g1 g2) ⟩
  winding (∙-π₁ (looping g1) (looping g2))
  ≡⟨ {!   !} ⟩
  m (winding (looping g1)) (winding (looping g2))
  ≡⟨ cong (λ x → m x (winding (looping g2))) ind1 ⟩
  m g1 (winding (looping g2))
  ≡⟨ cong (λ x → m g1 x) ind2 ⟩
  m g1 g2 ∎

e-ind : ∀{ℓ}{A : Type ℓ} → winding (looping {A = A} e) ≡ e
e-ind =
  winding (looping e)
  ≡⟨ cong winding (IsGroupHom.pres1 (loopingHom .snd)) ⟩
  winding 1π₁
  ≡⟨ {!   !} ⟩
  e ∎

inv-ind : ∀{ℓ}{A : Type ℓ} → (g : FreeGroup A) → winding (looping g) ≡ g → winding (looping (inv g)) ≡ inv g
inv-ind g ind =
  winding (looping (inv g))
  ≡⟨ cong winding (IsGroupHom.presinv (loopingHom .snd) g) ⟩
  winding (invπ₁ (looping g))
  ≡⟨ {!   !} ⟩
  inv (winding (looping g))
  ≡⟨ cong inv ind ⟩
  inv g ∎

right-homotopy : ∀{ℓ}{A : Type ℓ} → (g : FreeGroup A) → winding (looping g) ≡ g
right-homotopy = elimProp Bprop η-ind m-ind e-ind inv-ind
