{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)

open import WA.WA
open import WA.FreeGroupoid
open import WA.GroupoidIsomorphisms
open import WA.CodeWindingLooping

module WA.RightHomotopy where

postulate nMult : ∀ {ℓ}{A : Type ℓ} → ∀ (g1 g2 : FreeGroupoid A) → ua (equivs g1) ∙ ua (equivs g2) ≡ ua (equivs (m(g1 , g2)))
postulate nId : ∀ {ℓ}{A : Type ℓ} → refl {x = FreeGroupoid A} ≡ ua (equivs e)
postulate nInv : ∀ {ℓ}{A : Type ℓ} → ∀ (g : FreeGroupoid A) → sym (ua (equivs g)) ≡ ua (equivs (inv g))

naturalityOfUaPaths : ∀ {ℓ}{A : Type ℓ} → ∀ (g : FreeGroupoid A) → cong code (looping g) ≡ ua (equivs g)
naturalityOfUaPaths (η a) =
  cong code (looping (η a))
  ≡⟨ refl ⟩
  cong code (loop a)
  ≡⟨ refl ⟩
  pathsInU (η a)
  ≡⟨ refl ⟩
  ua (equivs (η a)) ∎
naturalityOfUaPaths (m(g1 , g2)) =
  cong code (looping (m(g1 , g2)))
  -- ≡⟨ refl ⟩
  -- cong code ((looping g1) ∙ (looping g2))
  -- ≡⟨ refl ⟩
  -- cong code (looping g1) ∙ cong code (looping g2)
  ≡⟨ cong (λ x → x ∙ cong code (looping g2)) (naturalityOfUaPaths g1) ⟩
  ua (equivs g1) ∙ cong code (looping g2)
  ≡⟨ cong (λ x → (ua (equivs g1)) ∙ x) (naturalityOfUaPaths g2) ⟩
  ua (equivs g1) ∙ ua (equivs g2)
  ≡⟨ nMult g1 g2 ⟩
  ua (equivs (m(g1 , g2))) ∎
naturalityOfUaPaths {A = A} e =
  cong code (looping e)
  ≡⟨ refl ⟩
  cong code (refl {x = base})
  ≡⟨ refl ⟩
  refl {x = FreeGroupoid A}
  ≡⟨ nId ⟩
  ua (equivs e) ∎
naturalityOfUaPaths (inv g) =
  cong code (looping (inv g))
  ≡⟨ refl ⟩
  cong code (sym (looping g))
  ≡⟨ refl ⟩
  sym (cong code (looping g))
  ≡⟨ cong sym (naturalityOfUaPaths g) ⟩
  sym (ua (equivs g))
  ≡⟨ nInv g ⟩
  ua (equivs (inv g)) ∎
naturalityOfUaPaths (assoc g1 g2 g3 i) = s i where
  -- cong code (looping (m(g1 , m(g2 , g3)))) ----------- l0/a₀₋ -----------→ ua (equivs (m(g1 , m(g2 , g3))))
  --         |                                                                            |
  --         a₋₀                                                                          a₋₁
  --         ↓                                                                            ↓
  -- cong code (looping (m(m(g1 , g2) , g3))) ----------- l1/a₁₋ -----------→ ua (equivs (m(m(g1 , g2) , g3)))
  postulate s : PathP (λ i → cong code (looping (assoc g1 g2 g3 i)) ≡ ua ( equivs (assoc g1 g2 g3 i))) (naturalityOfUaPaths (m(g1 , m(g2 , g3)))) (naturalityOfUaPaths (m(m(g1 , g2) , g3)))
naturalityOfUaPaths (idr g i) = s i where
  postulate s : PathP (λ i → cong code (looping (idr g i)) ≡ ua ( equivs (idr g i))) (naturalityOfUaPaths g) (naturalityOfUaPaths (m(g , e)))
naturalityOfUaPaths (idl g i) = s i where
  postulate s : PathP (λ i → cong code (looping (idl g i)) ≡ ua ( equivs (idl g i))) (naturalityOfUaPaths g) (naturalityOfUaPaths (m(e , g)))
naturalityOfUaPaths (invr g i) = s i where
  postulate s : PathP (λ i → cong code (looping (invr g i)) ≡ ua ( equivs (invr g i))) (naturalityOfUaPaths (m(g , inv g))) (naturalityOfUaPaths e)
naturalityOfUaPaths (invl g i) = s i where
  postulate s : PathP (λ i → cong code (looping (invl g i)) ≡ ua ( equivs (invl g i))) (naturalityOfUaPaths (m(inv g , g))) (naturalityOfUaPaths e)


right-homotopy : ∀ {ℓ}{A : Type ℓ} → ∀ (g : FreeGroupoid A) → winding (looping g) ≡ g
right-homotopy g =
  winding (looping g)
  ≡⟨ refl ⟩
  transport (cong code (looping g)) e
  ≡⟨ cong (λ s → transport s e) (naturalityOfUaPaths g)⟩
  transport (pathsInU g) e
  ≡⟨ refl ⟩
  transport (ua (equivs g)) e
  ≡⟨ uaβ (equivs g) e ⟩
  equivFun (equivs g) e
  ≡⟨ refl ⟩
  m( e , g)
  ≡⟨ sym (idl g) ⟩
  g ∎
