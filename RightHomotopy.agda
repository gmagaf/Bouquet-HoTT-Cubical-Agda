{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)
open import Cubical.Foundations.Transport using(substComposite)

open import WA.WA
open import WA.FreeGroupoid
open import WA.GroupoidIsomorphisms
open import WA.CodeWindingLooping

open import WA.PathNaturality using (assocFunctoriality ; uaAssocFunctoriality)

module WA.RightHomotopy where

postulate
  naturalityOfUaPaths : ∀ {ℓ}(A : Type ℓ) → ∀ (g : FreeGroupoid A) → cong (code A) (looping A g) ≡ ua (equivs g)


-- naturalityOfUaPaths : ∀ {ℓ}(A : Type ℓ) → ∀ (g : FreeGroupoid A) → cong (code A) (looping A g) ≡ ua (equivs g)
-- naturalityOfUaPaths A (η a) =
--   cong (code A) (looping A (η a))
--   ≡⟨ refl ⟩
--   cong (code A) (loop a)
--   ≡⟨ refl ⟩
--   pathsInU (η a)
--   ≡⟨ refl ⟩
--   ua (equivs (η a)) ∎
-- naturalityOfUaPaths A (m(g1 , g2)) =
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
-- naturalityOfUaPaths A e =
--   cong (code A) (looping A e)
--   ≡⟨ refl ⟩
--   cong (code A) (refl {x = base})
--   ≡⟨ refl ⟩
--   refl {x = FreeGroupoid A}
--   ≡⟨ sym uaIdEquiv ⟩
--   ua (idEquiv (FreeGroupoid A) )
--   ≡⟨ cong (λ s → ua s) naturalityOfIdEquivs ⟩
--   ua (equivs e) ∎
-- naturalityOfUaPaths A (inv g) =
--   cong (code A) (looping A (inv g))
--   ≡⟨ refl ⟩
--   cong (code A) (sym (looping A g))
--   ≡⟨ refl ⟩
--   sym (cong (code A) (looping A g))
--   ≡⟨ cong sym (naturalityOfUaPaths A g) ⟩
--   sym (ua (equivs g))
--   ≡⟨ sym (uaInvEquiv (equivs g)) ⟩
--   ua (invEquiv (equivs g))
--   ≡⟨ cong ua (naturalityOfInvEquivs g) ⟩
--   ua (equivs (inv g)) ∎
-- naturalityOfUaPaths A (assoc g1 g2 g3 i) =
--   cong (code A) (looping A (assoc g1 g2 g3 i))
--   ≡⟨ refl ⟩
--   cong (code A) (pathAssoc (looping A g1) (looping A g2) (looping A g3) i)
--   ≡⟨ refl ⟩
--   cong (cong (code A)) (pathAssoc (looping A g1) (looping A g2) (looping A g3)) i
--   ≡⟨ assocFunctoriality (code A) (looping A g1) (looping A g2) (looping A g3) i ⟩
--   pathAssoc (cong (code A) (looping A g1)) (cong (code A) (looping A g2)) (cong (code A) (looping A g3)) i
--   ≡⟨ cong (λ s1 → pathAssoc s1 (cong (code A) (looping A g2)) (cong (code A) (looping A g3)) i) (naturalityOfUaPaths A g1) ⟩
--   pathAssoc (ua (equivs g1)) (cong (code A) (looping A g2)) (cong (code A) (looping A g3)) i
--   ≡⟨ cong (λ s2 → pathAssoc (ua (equivs g1)) s2 (cong (code A) (looping A g3)) i) (naturalityOfUaPaths A g2) ⟩
--   pathAssoc (ua (equivs g1)) (ua (equivs g2)) (cong (code A) (looping A g3)) i
--   ≡⟨ cong (λ s3 → pathAssoc (ua (equivs g1)) (ua (equivs g2)) s3 i) (naturalityOfUaPaths A g3) ⟩
--   pathAssoc (ua (equivs g1)) (ua (equivs g2)) (ua (equivs g3)) i
--   ≡⟨ uaAssocFunctoriality (equivs g1) (equivs g2) (equivs g3) i ⟩
--   cong ua (compEquiv-assoc (equivs g1) (equivs g2) (equivs g3)) i
--   ≡⟨ refl ⟩
--   ua ((compEquiv-assoc (equivs g1) (equivs g2) (equivs g3)) i)
--   ≡⟨ cong ua (naturalityOfAssocEquivs g1 g2 g3 i) ⟩
--   ua (equivs (assoc g1 g2 g3 i)) ∎

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
