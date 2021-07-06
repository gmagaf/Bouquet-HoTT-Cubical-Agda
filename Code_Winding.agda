{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
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

winding : ∀ {ℓ}(A : Type ℓ) → base ≡ base → (FreeGroupoid A) → (FreeGroupoid A)
winding A l g = transport (cong (code A) l) g

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

naturalityOfUaPaths : ∀ {ℓ}(A : Type ℓ) → ∀ (g1 : FreeGroupoid A) → cong (code A) (looping A g1) ≡ ua (equivs g1)
naturalityOfUaPaths A (η a) =
  cong (code A) (looping A (η a))
  ≡⟨ refl ⟩
  cong (code A) (loop a)
  ≡⟨ refl ⟩
  pathsInU (η a)
  ≡⟨ refl ⟩
  ua (equivs (η a)) ∎
naturalityOfUaPaths A (m(g1 , g2)) =
  cong (code A) (looping A (m(g1 , g2)))
  ≡⟨ refl ⟩
  cong (code A) ((looping A g1) ∙ (looping A g2))
  ≡⟨ refl ⟩
  cong (code A) (looping A g1) ∙ cong (code A) (looping A g2)
  ≡⟨ cong (λ x → x ∙ cong (code A) (looping A g2)) (naturalityOfUaPaths A g1) ⟩
  ua (equivs g1) ∙ cong (code A) (looping A g2)
  ≡⟨ cong (λ x → (ua (equivs g1)) ∙ x) (naturalityOfUaPaths A g2) ⟩
  ua (equivs g1) ∙ ua (equivs g2)
  ≡⟨ sym (uaCompEquiv (equivs g1) (equivs g2)) ⟩
  ua (compEquiv (equivs g1) (equivs g2))
  ≡⟨ cong (λ x → ua x) (naturalityOfEquivs g1 g2) ⟩
  ua (equivs (m(g1 , g2))) ∎
naturalityOfUaPaths A (FreeGroupoid.assoc g1 g2 g3 i)
  cong (code A) (looping A (FreeGroupoid.assoc g1 g2 g3 i))
  ≡⟨ refl ⟩
  cong (code A) (Cubical.Foundations.GroupoidLaws.assoc (looping A g1) (looping A g2) (looping A g3) i)
  ≡⟨⟩
-- naturalityOfUaPaths A e
-- naturalityOfUaPaths A (inv g1)
-- naturalityOfUaPaths A (FreeGroupoid.assoc g1 g2 g3 i)
-- naturalityOfUaPaths A (idr g1 i)
-- naturalityOfUaPaths A (idl g1 i)
-- naturalityOfUaPaths A (invr g1 i)
-- naturalityOfUaPaths A (invl g1 i)


-- windingOfLoopsIsMulti : ∀ {ℓ}(A : Type ℓ) → ∀ (g1 g2 : FreeGroupoid A) → winding A (looping A g1) g2 ≡ m(g2 , g1)
-- windingOfLoopsIsMulti A (η a) g2 =
--   winding A (looping A (η a)) g2
--   ≡⟨ refl ⟩
--   transport (cong (code A) (loop a)) g2
--   ≡⟨ refl ⟩
--   transport (λ i → pathsInU a i) g2
--   ≡⟨ refl ⟩
--   transport (ua (equivs a)) g2
--   ≡⟨ uaβ (equivs a) g2 ⟩
--   automorhpism a g2
--   ≡⟨ refl ⟩
--   m(g2 , η a) ∎
-- windingOfLoopsIsMulti A (m(k1 , k2)) g2 =
--   winding A (looping A (m(k1 , k2))) g2
--   ≡⟨ refl ⟩
--   transport (cong (code A) ((looping A k1) ∙ (looping A k2))) g2
--   ≡⟨ refl ⟩
--   transport ((cong (code A) (looping A k1)) ∙ (cong (code A) (looping A k2))) g2
--   ≡⟨ refl ⟩
--   subst (λ x → x) ((cong (code A) (looping A k1)) ∙ (cong (code A) (looping A k2))) g2
--   ≡⟨ substComposite (λ x → x) (cong (code A) (looping A k1)) (cong (code A) (looping A k2)) g2 ⟩
--   subst (λ x → x) (cong (code A) (looping A k2)) (subst (λ x → x) (cong (code A) (looping A k1)) g2)
--   ≡⟨ refl ⟩
--   transport (cong (code A) (looping A k2)) (transport (cong (code A) (looping A k1)) g2)
--   ≡⟨ cong (λ x → transport (cong (code A) (looping A k2)) x) (windingOfLoopsIsMulti A k1 g2) ⟩
--   transport (cong (code A) (looping A k2)) (m(g2 , k1))
--   ≡⟨ windingOfLoopsIsMulti A k2 (m(g2 , k1)) ⟩
--   m((m(g2 , k1)) , k2)
--   ≡⟨ sym (FreeGroupoid.assoc g2 k1 k2) ⟩
--   m(g2 , m(k1 , k2)) ∎
-- windingOfLoopsIsMulti A e g2 =
--   winding A (looping A e) g2
--   ≡⟨ refl ⟩
--   transport (cong (code A) (refl { x = base })) g2
--   ≡⟨ refl ⟩
--   transport (refl { x = code A base}) g2
--   ≡⟨ transportRefl g2 ⟩
--   g2
--   ≡⟨ sym (idr g2) ⟩
--   m(g2 , e) ∎
-- windingOfLoopsIsMulti A (inv g1) g2 =
--   winding A (looping A (inv g1)) g2
--   ≡⟨ refl ⟩
--   transport (cong (code A) (sym (looping A g1))) g2
--   ≡⟨ refl ⟩
--   transport (sym (cong (code A) (looping A g1))) g2
--   ≡⟨ refl ⟩





-- lhomotopy : ∀ {ℓ}(A : Type ℓ) → ∀ (g : FreeGroupoid A) → winding A (looping A g) ≡ g
