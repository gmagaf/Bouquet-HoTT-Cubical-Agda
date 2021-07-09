{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport using(substComposite)

open import WA.WA
open import WA.FreeGroupoid
open import WA.GroupoidIsomorphisms

module WA.Code_Winding where

code : ∀ {ℓ}(A : Type ℓ) → (W A) → Type ℓ
code A base       = (FreeGroupoid A)
code A (loop a i) = pathsInU (η a) i

winding : ∀ {ℓ}(A : Type ℓ) → base ≡ base → (FreeGroupoid A)
winding A l = transport (cong (code A) l) e

looping : ∀ {ℓ}(A : Type ℓ) → (FreeGroupoid A) → base ≡ base
looping A (η a) = loop a
looping A (m (g1 , g2)) = (looping A g1) ∙ (looping A g2)
looping A e = refl
looping A (inv x) = sym (looping A x)
looping A (FreeGroupoid.assoc x y z i) = Cubical.Foundations.GroupoidLaws.assoc (looping A x) (looping A y) (looping A z) i
looping A (idr x i) = sym (rUnit (looping A x)) i
looping A (idl x i) = sym (lUnit (looping A x)) i
looping A (invr x i) = rCancel (looping A x) i
looping A (invl x i) = lCancel (looping A x) i

postulate
  naturalityOfUaPaths : ∀ {ℓ}(A : Type ℓ) → ∀ (g : FreeGroupoid A) → cong (code A) (looping A g) ≡ ua (equivs g)


-- naturalityOfUaPathsC : ∀ {ℓ}(A : Type ℓ) → ∀ (g : FreeGroupoid A) → cong (code A) (looping A g) ≡ ua (equivs g)
-- naturalityOfUaPathsC A (η a) =
--   cong (code A) (looping A (η a))
--   ≡⟨ refl ⟩
--   cong (code A) (loop a)
--   ≡⟨ refl ⟩
--   pathsInU (η a)
--   ≡⟨ refl ⟩
--   ua (equivs (η a)) ∎
-- naturalityOfUaPathsC A (m(g1 , g2)) =
--   cong (code A) (looping A (m(g1 , g2)))
--   ≡⟨ refl ⟩
--   cong (code A) ((looping A g1) ∙ (looping A g2))
--   ≡⟨ refl ⟩
--   cong (code A) (looping A g1) ∙ cong (code A) (looping A g2)
--   ≡⟨ cong (λ x → x ∙ cong (code A) (looping A g2)) (naturalityOfUaPaths A g1) ⟩
--   ua (equivs g1) ∙ cong (code A) (looping A g2)
--   ≡⟨ cong (λ x → (ua (equivs g1)) ∙ x) (naturalityOfUaPaths A g2) ⟩
--   ua (equivs g1) ∙ ua (equivs g2)
--   ≡⟨ sym (uaCompEquiv (equivs g1) (equivs g2)) ⟩
--   ua (compEquiv (equivs g1) (equivs g2))
--   ≡⟨ cong (λ x → ua x) (naturalityOfEquivs g1 g2) ⟩
--   ua (equivs (m(g1 , g2))) ∎
-- naturalityOfUaPathsC A e =
--   cong (code A) (looping A e)
--   ≡⟨ refl ⟩
--   cong (code A) (refl {x = base})
--   ≡⟨ refl ⟩
--   refl {x = FreeGroupoid A}
--   ≡⟨ sym uaIdEquiv ⟩
--   ua (idEquiv (FreeGroupoid A) )
--   ≡⟨ cong (λ s → ua s) naturalityOfIdEquivs ⟩
--   ua (equivs e) ∎
-- naturalityOfUaPathsC A (inv g) =
--   cong (code A) (looping A (inv g))
--   ≡⟨ refl ⟩
--   cong (code A) (sym (looping A g))
--   ≡⟨ refl ⟩
--   sym (cong (code A) (looping A g))
--   ≡⟨ cong sym (naturalityOfUaPathsC A g) ⟩
--   sym (ua (equivs g))
--   ≡⟨ sym (uaInvEquiv (equivs g)) ⟩
--   ua (invEquiv (equivs g))
--   ≡⟨ cong ua (naturalityOfInvEquivs g) ⟩
--   ua (equivs (inv g)) ∎

-- naturalityOfUaPaths A (FreeGroupoid.assoc g1 g2 g3 i)
-- naturalityOfUaPaths A (idr g1 i)
-- naturalityOfUaPaths A (idl g1 i)
-- naturalityOfUaPaths A (invr g1 i)
-- naturalityOfUaPaths A (invl g1 i)

right-homotopy : ∀ {ℓ}(A : Type ℓ) → ∀ (g : FreeGroupoid A) → winding A (looping A g) ≡ g
right-homotopy A g =
  winding A (looping A g)
  ≡⟨ refl ⟩
  transport (cong (code A) (looping A g)) e
  ≡⟨ cong (λ s → transport s e) (naturalityOfUaPaths A g)⟩
  transport (ua (equivs g)) e
  ≡⟨ uaβ (equivs g) e ⟩
  equivFun (equivs g) e
  ≡⟨ refl ⟩
  automorhpism g e
  ≡⟨ refl ⟩
  m(e , g)
  ≡⟨ idl g ⟩
  g ∎
