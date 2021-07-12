{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Foundations.Path using (Square≃doubleComp)

open import WA.WA
open import WA.FreeGroupoid
open import WA.GroupoidIsomorphisms
open import WA.CodeWindingLooping

module WA.RightHomotopy where

-- postulate
--   naturalityOfUaPaths : ∀ {ℓ}(A : Type ℓ) → ∀ (g : FreeGroupoid A) → cong (code A) (looping A g) ≡ ua (equivs g)

compSquares :
  ∀ {ℓ}{A : Type ℓ}
  {a₀₀ a₀₁ a₀₂ : A} {a₀ₗ : a₀₀ ≡ a₀₁} {a₀ᵣ : a₀₁ ≡ a₀₂}
  {a₁₀ a₁₁ a₁₂ : A} {a₁ₗ : a₁₀ ≡ a₁₁} {a₁ᵣ : a₁₁ ≡ a₁₂}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} {a₋₂ : a₀₂ ≡ a₁₂} →
  PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀ₗ a₁ₗ → PathP (λ i → a₋₁ i ≡ a₋₂ i) a₀ᵣ a₁ᵣ → PathP (λ i → a₋₀ i ≡ a₋₂ i) (a₀ₗ ∙ a₀ᵣ) (a₁ₗ ∙ a₁ᵣ)
compSquares s1 s2 = λ i → (s1 i) ∙ (s2 i)


naturalityOfUaPaths : ∀ {ℓ}(A : Type ℓ) → ∀ (g : FreeGroupoid A) → cong (code A) (looping A g) ≡ ua (equivs g)
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
  -- ≡⟨ refl ⟩
  -- cong (code A) ((looping A g1) ∙ (looping A g2))
  -- ≡⟨ refl ⟩
  -- cong (code A) (looping A g1) ∙ cong (code A) (looping A g2)
  ≡⟨ cong (λ x → x ∙ cong (code A) (looping A g2)) (naturalityOfUaPaths A g1) ⟩
  ua (equivs g1) ∙ cong (code A) (looping A g2)
  ≡⟨ cong (λ x → (ua (equivs g1)) ∙ x) (naturalityOfUaPaths A g2) ⟩
  ua (equivs g1) ∙ ua (equivs g2)
  ≡⟨ sym (uaCompEquiv (equivs g1) (equivs g2)) ⟩
  ua (compEquiv (equivs g1) (equivs g2))
  ≡⟨ cong (λ x → ua x) (naturalityOfEquivs g1 g2) ⟩
  ua (equivs (m(g1 , g2))) ∎
naturalityOfUaPaths A e =
  cong (code A) (looping A e)
  ≡⟨ refl ⟩
  cong (code A) (refl {x = base})
  ≡⟨ refl ⟩
  refl {x = FreeGroupoid A}
  ≡⟨ sym uaIdEquiv ⟩
  ua (idEquiv (FreeGroupoid A) )
  ≡⟨ cong (λ s → ua s) naturalityOfIdEquivs ⟩
  ua (equivs e) ∎
naturalityOfUaPaths A (inv g) =
  cong (code A) (looping A (inv g))
  ≡⟨ refl ⟩
  cong (code A) (sym (looping A g))
  ≡⟨ refl ⟩
  sym (cong (code A) (looping A g))
  ≡⟨ cong sym (naturalityOfUaPaths A g) ⟩
  sym (ua (equivs g))
  ≡⟨ sym (uaInvEquiv (equivs g)) ⟩
  ua (invEquiv (equivs g))
  ≡⟨ cong ua (naturalityOfInvEquivs g) ⟩
  ua (equivs (inv g)) ∎
naturalityOfUaPaths A (assoc g1 g2 g3 i) = s i where
  aux1 : cong (code A) (looping A (m(g2 , g3))) ≡ ua (equivs (m(g2 , g3)))
  aux1 =
    cong (λ x → x ∙ cong (code A) (looping A g3)) (naturalityOfUaPaths A g2) ∙
    cong (λ x → (ua (equivs g2)) ∙ x) (naturalityOfUaPaths A g3) ∙
    sym (uaCompEquiv (equivs g2) (equivs g3)) ∙
    cong ua (naturalityOfEquivs g2 g3) ∙ refl
  aux2 : cong (code A) (looping A (m(g1 , g2))) ≡ ua (equivs (m(g1 , g2)))
  aux2 =
    cong (λ x → x ∙ cong (code A) (looping A g2)) (naturalityOfUaPaths A g1) ∙
    cong (λ x → (ua (equivs g1)) ∙ x) (naturalityOfUaPaths A g2) ∙
    sym (uaCompEquiv (equivs g1) (equivs g2)) ∙
    cong ua (naturalityOfEquivs g1 g2) ∙ refl
  l0  : cong (code A) (looping A (m(g1 , m(g2 , g3)))) ≡ ua (equivs (m(g1 , m(g2 , g3))))
  l0 = naturalityOfUaPaths A (m(g1 , m(g2 , g3)))
  l1 : cong (code A) (looping A (m(m(g1 , g2) , g3))) ≡ ua (equivs (m(m(g1 , g2) , g3)))
  l1 = naturalityOfUaPaths A (m(m(g1 , g2) , g3))
  a₀₀ = cong (code A) (looping A (m(g1 , m(g2 , g3))))
  a₀₁ = ua (equivs (m(g1 , m(g2 , g3))))
  a₁₀ = cong (code A) (looping A (m(m(g1 , g2) , g3)))
  a₁₁ = ua (equivs (m(m(g1 , g2) , g3)))
  a₀₋ : a₀₀ ≡ a₀₁
  a₀₋ = l0
  a₁₋ : a₁₀ ≡ a₁₁
  a₁₋ = l1
  a₋₀ : a₀₀ ≡ a₁₀
  a₋₀ = λ i → cong (code A) (looping A (assoc g1 g2 g3 i))
  a₋₁ : a₀₁ ≡ a₁₁
  a₋₁ = λ i → ua (equivs (assoc g1 g2 g3 i))
  square = Square a₀₋ a₁₋ a₋₀ a₋₁
  -- postulate s : square
  -- postulate p : PathP (λ i → cong (code A) (looping A (assoc g1 g2 g3 i)) ≡ ua (equivs (assoc g1 g2 g3 i))) l0 l1
  -- cong (code A) (looping A (m(g1 , m(g2 , g3)))) ----------- l0/a₀₋ -----------→ ua (equivs (m(g1 , m(g2 , g3))))
  --         |                                                                            |
  --         a₋₀                                                                          a₋₁
  --         ↓                                                                            ↓
  -- cong (code A) (looping A (m(m(g1 , g2) , g3))) ----------- l1/a₁₋ -----------→ ua (equivs (m(m(g1 , g2) , g3)))
  v1 : ua (equivs g1) ∙ cong (code A) (looping A (m(g2 , g3))) ≡ ua (equivs (m(g1 , g2))) ∙ cong (code A) (looping A g3)
  v1 =
    ua (equivs g1) ∙ cong (code A) (looping A (m(g2 , g3)))
    ≡⟨ cong (λ s → ua (equivs g1) ∙ s) aux1 ⟩
    ua (equivs g1) ∙ ua (equivs (m(g2 , g3)))
    ≡⟨ sym (uaCompEquiv (equivs g1) (equivs (m(g2 , g3)))) ⟩
    ua (compEquiv (equivs g1) (equivs (m(g2 , g3))))
    ≡⟨ cong ua (naturalityOfEquivs g1 (m(g2 , g3))) ⟩
    ua (equivs (m(g1 , m(g2 , g3))))
    ≡⟨ cong (λ x → ua (equivs x)) (assoc g1 g2 g3) ⟩
    ua (equivs (m(m (g1 , g2) , g3)))
    ≡⟨ cong ua (sym (naturalityOfEquivs (m (g1 , g2)) g3)) ⟩
    ua (compEquiv (equivs (m (g1 , g2))) (equivs g3))
    ≡⟨ uaCompEquiv (equivs (m (g1 , g2))) (equivs g3) ⟩
    ua (equivs (m (g1 , g2))) ∙ ua (equivs g3)
    ≡⟨ cong (λ s → ua (equivs (m (g1 , g2))) ∙ s) (sym (naturalityOfUaPaths A g3)) ⟩
    ua (equivs (m(g1 , g2))) ∙ cong (code A) (looping A g3) ∎
  v2 : ua (equivs g1) ∙ ua (equivs (m(g2 , g3))) ≡ ua (equivs (m(g1 , g2))) ∙ ua (equivs g3)
  v2 =
    ua (equivs g1) ∙ ua (equivs (m(g2 , g3)))
    ≡⟨ sym (uaCompEquiv (equivs g1) (equivs (m(g2 , g3)))) ⟩
    ua (compEquiv (equivs g1) (equivs (m(g2 , g3))))
    ≡⟨ cong ua (naturalityOfEquivs g1 (m(g2 , g3))) ⟩
    ua (equivs (m(g1 , m(g2 , g3))))
    ≡⟨ cong (λ x → ua (equivs x)) (assoc g1 g2 g3) ⟩
    ua (equivs (m(m(g1 , g2) , g3)))
    ≡⟨ cong ua (sym (naturalityOfEquivs (m(g1 , g2)) g3)) ⟩
    ua (compEquiv (equivs (m(g1 , g2))) (equivs g3) )
    ≡⟨ uaCompEquiv (equivs (m(g1 , g2))) (equivs g3) ⟩
    ua (equivs (m(g1 , g2))) ∙ ua (equivs g3) ∎
  v3 : ua (compEquiv (equivs g1) (equivs (m(g2 , g3)))) ≡ ua (compEquiv (equivs (m(g1 , g2))) (equivs g3))
  v3 =
    ua (compEquiv (equivs g1) (equivs (m(g2 , g3))))
    ≡⟨ cong ua (naturalityOfEquivs g1 (m(g2 , g3))) ⟩
    ua (equivs (m(g1 , m(g2 , g3))))
    ≡⟨ cong (λ x → ua (equivs x)) (assoc g1 g2 g3) ⟩
    ua (equivs (m(m(g1 , g2) , g3)))
    ≡⟨ cong ua (sym (naturalityOfEquivs (m(g1 , g2)) g3)) ⟩
    ua (compEquiv (equivs (m(g1 , g2))) (equivs g3)) ∎
  postulate s1 : PathP (λ i → cong (code A) (looping A (assoc g1 g2 g3 i)) ≡ v1 i) (cong (λ x → x ∙ cong (code A) (looping A (m(g2 , g3)))) (naturalityOfUaPaths A g1)) (cong (λ x → x ∙ cong (code A) (looping A g3)) (aux2))
  postulate s2 : PathP (λ i → v1 i ≡ v2 i) (cong (λ x → (ua (equivs g1)) ∙ x) (aux1)) (cong (λ x → (ua (equivs (m(g1 , g2)))) ∙ x) (naturalityOfUaPaths A g3))
  postulate s3 : PathP (λ i → v2 i ≡ v3 i) (sym (uaCompEquiv (equivs g1) (equivs (m(g2 , g3))))) (sym (uaCompEquiv (equivs (m(g1 , g2))) (equivs g3)))
  postulate s4 : PathP (λ i → v3 i ≡ ua (equivs (assoc g1 g2 g3 i))) (cong ua (naturalityOfEquivs g1 (m(g2 , g3)))) (cong ua (naturalityOfEquivs (m(g1 , g2)) g3))
  -- s4 = λ i →
  -- ua (compEquiv (equivs g1) (equivs (m(g2 , g3)))) --- ua (compEquiv (equivs g1) (compEquiv (equivs g2) (equivs g3))) --- l0 ----- ua (equivs g1 * (g2 * g3))
  --     |                                                  |                                                                          |
  --     |v3 i                                              | ua(compEquiv-assoc (equivs g1) (equivs g2) (equivs g3) i)                |ua (equivs (assoc g1 g2 g3 i)))
  --     |                                                  |                                                                          |
  -- ua (compEquiv (equivs (m(g1 , g2))) (equivs g3)) --- ua (compEquiv (compEquiv (equivs g1) (equivs g2)) (equivs g3)) --- l1 ----- ua (equivs (g1 * g2) * g3)
  s5 : PathP (λ i → ua (equivs (assoc g1 g2 g3 i)) ≡ ua (equivs (assoc g1 g2 g3 i))) refl refl
  s5 = λ i → refl
  s : square
  s = compSquares s1 (compSquares s2 (compSquares s3 (compSquares s4 s5)))
naturalityOfUaPaths A (idr g i) = s i where
  l0  : cong (code A) (looping A (m(g , e))) ≡ ua (equivs (m(g , e)))
  l0 = naturalityOfUaPaths A (m(g , e))
  l1 : cong (code A) (looping A g) ≡ ua (equivs g)
  l1 = naturalityOfUaPaths A g
  a₀₀ = cong (code A) (looping A (m(g , e)))
  a₀₁ = ua (equivs (m(g , e)))
  a₁₀ = cong (code A) (looping A g)
  a₁₁ = ua (equivs g)
  a₀₋ : a₀₀ ≡ a₀₁
  a₀₋ = l0
  a₁₋ : a₁₀ ≡ a₁₁
  a₁₋ = l1
  a₋₀ : a₀₀ ≡ a₁₀
  a₋₀ = λ i → cong (code A) (looping A (idr g i))
  a₋₁ : a₀₁ ≡ a₁₁
  a₋₁ = λ i → ua (equivs (idr g i))
  square = Square a₀₋ a₁₋ a₋₀ a₋₁
  postulate s : square
  s' : PathP (λ i → a₋₀ (~ i) ≡ (sym a₋₁) i) l1 (a₋₀ ∙∙ l1 ∙∙ (sym a₋₁))
  s' = doubleCompPath-filler (λ i → cong (code A) (looping A (idr g i))) l1 (sym (λ i → ua (equivs (idr g i))))
-- λ i → cong (code A) (looping A (idr g i)) ∙ naturalityOfUaPaths A g ∙ λ i → ua (equivs (idr g (~ i)))
-- ≡ naturalityOfUaPaths A (m(g , e))
-- = cong (λ x → x ∙ cong (code A) (looping A e)) (naturalityOfUaPaths A g) ∙
--   cong (λ x → (ua (equivs g)) ∙ x) (naturalityOfUaPaths A e) ∙
--   sym (uaCompEquiv (equivs g) (equivs e)) ∙
--   cong ua (naturalityOfEquivs g e) ∙ refl
-- = (naturalityOfUaPaths A g) ∙
--   (ua (equivs g)) ∙
--   sym (equivs g) ∙
--   ua (equivs g) ∙ refl
-- = (naturalityOfUaPaths A g)
-- Sooo
-- we need!!!
-- λ i → cong (code A) (looping A (idr g i)) ∙ naturalityOfUaPaths A g
-- ≡ naturalityOfUaPaths A (m(g , e)) ∙ λ i → ua (equivs (idr g i))
-- TODO fix this mess:
-- equivs m(g , e) =? equivs (idr g i) =? equivs g
-- and
-- cong (code A) (looping A (idr g i)) =? cong (code A) (looping A g)
-- so the above becomes refl ∙ naturalityOfUaPaths A g ≡ naturalityOfUaPaths A g ∙ refl


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
