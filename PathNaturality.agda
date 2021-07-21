{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function

open import Cubical.Data.Unit.Base

module WA.PathNaturality where


compSquares :
  ∀ {ℓ}{A : Type ℓ}
  {a₀₀ a₀₁ a₀₂ : A} {a₀ₗ : a₀₀ ≡ a₀₁} {a₀ᵣ : a₀₁ ≡ a₀₂}
  {a₁₀ a₁₁ a₁₂ : A} {a₁ₗ : a₁₀ ≡ a₁₁} {a₁ᵣ : a₁₁ ≡ a₁₂}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} {a₋₂ : a₀₂ ≡ a₁₂} →
  PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀ₗ a₁ₗ → PathP (λ i → a₋₁ i ≡ a₋₂ i) a₀ᵣ a₁ᵣ → PathP (λ i → a₋₀ i ≡ a₋₂ i) (a₀ₗ ∙ a₀ᵣ) (a₁ₗ ∙ a₁ᵣ)
compSquares s1 s2 = λ i → (s1 i) ∙ (s2 i)


assocLem1 : ∀ {ℓ ℓ'}{A : Type ℓ}{B : Type ℓ'}{x y z w : A} → (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → cong f (p ∙ (q ∙ r)) ≡ (cong f p) ∙ ((cong f q) ∙ (cong f r))
assocLem1 f p q r =
  cong f (p ∙ (q ∙ r))
  ≡⟨ cong-∙ f p (q ∙ r) ⟩
  (cong f p) ∙ (cong f (q ∙ r))
  ≡⟨ cong (λ s → (cong f p) ∙ s) (cong-∙ f q r) ⟩
  cong f p ∙ (cong f q ∙ cong f r) ∎

assocLem2 : ∀ {ℓ ℓ'}{A : Type ℓ}{B : Type ℓ'}{x y z w : A} → (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → cong f ((p ∙ q) ∙ r) ≡ ((cong f p) ∙ (cong f q)) ∙ (cong f r)
assocLem2 f p q r =
  cong f ((p ∙ q) ∙ r)
  ≡⟨ cong-∙ f (p ∙ q) r ⟩
  (cong f (p ∙ q)) ∙ (cong f r)
  ≡⟨ cong (λ s → s ∙ (cong f r)) (cong-∙ f p q) ⟩
  (cong f p ∙ cong f q) ∙ cong f r ∎

assocSquare : ∀ {ℓ ℓ'}{A : Type ℓ}{B : Type ℓ'}{x y z w : A} → (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → Type ℓ'
assocSquare f p q r = PathP (λ i → (cong (cong f) (pathAssoc p q r)) i ≡
                            (pathAssoc (cong f p) (cong f q) (cong f r)) i) l1 l2 where
  l1 : cong f (p ∙ (q ∙ r)) ≡ (cong f p) ∙ ((cong f q) ∙ (cong f r))
  l1 = assocLem1 f p q r
  l2 : cong f ((p ∙ q) ∙ r) ≡ ((cong f p) ∙ (cong f q)) ∙ (cong f r)
  l2 = assocLem2 f p q r

postulate
  assocFunctoriality : ∀ {ℓ ℓ'}{A : Type ℓ}{B : Type ℓ'}{x y z w : A} → (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → assocSquare f p q r

uaAssocLem1 : ∀ {ℓ}{A B C D : Type ℓ} → (e1 : A ≃ B) → (e2 : B ≃ C) → (e3 : C ≃ D) → ua e1 ∙ (ua e2 ∙ ua e3) ≡ ua (compEquiv e1 (compEquiv e2 e3))
uaAssocLem1 e1 e2 e3 =
  ua e1 ∙ (ua e2 ∙ ua e3)
  ≡⟨ cong (λ s → (ua e1) ∙ s) (sym (uaCompEquiv e2 e3)) ⟩
  ua e1 ∙ ua (compEquiv e2 e3)
  ≡⟨ sym (uaCompEquiv e1 (compEquiv e2 e3)) ⟩
  ua(compEquiv e1 (compEquiv e2 e3)) ∎

uaAssocLem2 : ∀ {ℓ}{A B C D : Type ℓ} → (e1 : A ≃ B) → (e2 : B ≃ C) → (e3 : C ≃ D) → (ua e1 ∙ ua e2) ∙ ua e3 ≡ ua (compEquiv (compEquiv e1 e2) e3)
uaAssocLem2 e1 e2 e3 =
  (ua e1 ∙ ua e2) ∙ ua e3
  ≡⟨ cong (λ s → s ∙ (ua e3)) (sym (uaCompEquiv e1 e2)) ⟩
  ua (compEquiv e1 e2) ∙ ua e3
  ≡⟨ sym (uaCompEquiv (compEquiv e1 e2) e3) ⟩
  ua(compEquiv (compEquiv e1 e2) e3) ∎

uaAssocSquare : ∀ {ℓ}{A B C D : Type ℓ} → (e1 : A ≃ B) → (e2 : B ≃ C) → (e3 : C ≃ D) → Type (ℓ-suc ℓ)
uaAssocSquare e1 e2 e3 = PathP (λ i → (pathAssoc (ua e1) (ua e2) (ua e3)) i ≡
                                      (cong ua (compEquiv-assoc e1 e2 e3)) i) l1 l2 where
  l1 : ua e1 ∙ (ua e2 ∙ ua e3) ≡ ua (compEquiv e1 (compEquiv e2 e3))
  l1 = uaAssocLem1 e1 e2 e3
  l2 : (ua e1 ∙ ua e2) ∙ ua e3 ≡ ua (compEquiv (compEquiv e1 e2) e3)
  l2 = uaAssocLem2 e1 e2 e3

postulate
  pathAssocRefl : ∀ {ℓ}{D : Type ℓ} → (i : I) → pathAssoc (refl {x = D}) (refl {x = D}) (refl {x = D}) i ≡ refl {x = refl {x = D}} i

tmp1 : ∀ {ℓ}(D : Type ℓ) → (i : I) → pathAssoc (ua (idEquiv D)) (ua (idEquiv D)) (ua (idEquiv D)) i ≡ refl {x = refl {x = D}} i
tmp1 D i =
  pathAssoc (ua (idEquiv D)) (ua (idEquiv D)) (ua (idEquiv D)) i
  ≡⟨ cong (λ s → pathAssoc s (ua (idEquiv D)) (ua (idEquiv D)) i) (uaIdEquiv {A = D}) ⟩
  (pathAssoc refl (ua (idEquiv D)) (ua (idEquiv D))) i
  ≡⟨ cong (λ s → pathAssoc refl s (ua (idEquiv D)) i) (uaIdEquiv {A = D}) ⟩
  (pathAssoc refl refl (ua (idEquiv D))) i
  ≡⟨ cong (λ s → pathAssoc refl refl s i) (uaIdEquiv {A = D}) ⟩
  (pathAssoc (refl {x = D}) (refl {x = D}) (refl {x = D})) i
  ≡⟨ pathAssocRefl {D = D} i ⟩
  refl {x = refl {x = D}} i ∎

tmp2 : ∀ {ℓ}(D : Type ℓ) → (i : I) → cong ua (compEquiv-assoc (idEquiv D) (idEquiv D) (idEquiv D)) i ≡ refl i
tmp2 D i =
  cong ua (compEquiv-assoc (idEquiv D) (idEquiv D) (idEquiv D)) i
  ≡⟨ refl ⟩
  ua (compEquiv-assoc (idEquiv D) (idEquiv D) (idEquiv D) i)
  ≡⟨ cong ua (equivEq refl) ⟩
  ua (refl {x = idEquiv D} i)
  ≡⟨ uaIdEquiv ⟩
  refl {x = D}
  ≡⟨ refl ⟩
  refl {x = refl {x = D}} i ∎

tmp3 : ∀ {ℓ}(D : Type ℓ) → (i : I) → pathAssoc (ua (idEquiv D)) (ua (idEquiv D)) (ua (idEquiv D)) i ≡ cong ua (compEquiv-assoc (idEquiv D) (idEquiv D) (idEquiv D)) i
tmp3 D i = (tmp1 D i) ∙ (sym (tmp2 D i))

r3 : ∀ {ℓ}{C D : Type ℓ} → (e3 : C ≃ D) → (i : I) →
    pathAssoc (ua (idEquiv C)) (ua (idEquiv C)) (ua e3) i ≡ cong ua (compEquiv-assoc (idEquiv C) (idEquiv C) e3) i
r3 {ℓ = ℓ}{C = C}{D = D} e3 i = EquivJ P r e3 where
  P : (C' : Type ℓ) → (e3' : C' ≃ D) → Type (ℓ-suc ℓ)
  P C' e3' = pathAssoc (ua (idEquiv C')) (ua (idEquiv C')) (ua e3') i ≡ cong ua (compEquiv-assoc (idEquiv C') (idEquiv C')  e3') i
  r : P D (idEquiv D)
  r = tmp3 D i

r2 : ∀ {ℓ}{B C D : Type ℓ} → (e2 : B ≃ C) → (e3 : C ≃ D) → (i : I) →
    pathAssoc (ua (idEquiv B)) (ua e2) (ua e3) i ≡ cong ua (compEquiv-assoc (idEquiv B) e2 e3) i
r2 {ℓ = ℓ}{B = B}{C = C}{D = D} e2 e3 i = EquivJ P r e2 where
  P : (B' : Type ℓ) → (e2' : B' ≃ C) → Type (ℓ-suc ℓ)
  P B' e2' = pathAssoc (ua (idEquiv B')) (ua e2') (ua e3) i ≡ cong ua (compEquiv-assoc (idEquiv B') e2' e3) i
  r : P C (idEquiv C)
  r = r3 e3 i

r1 : ∀ {ℓ}{A B C D : Type ℓ} → (e1 : A ≃ B) → (e2 : B ≃ C) → (e3 : C ≃ D) → (i : I) →
    pathAssoc (ua e1) (ua e2) (ua e3) i ≡ cong ua (compEquiv-assoc e1 e2 e3) i
r1 {ℓ = ℓ}{A = A}{B = B}{C = C}{D = D} e1 e2 e3 i = EquivJ P r e1 where
  P : (A' : Type ℓ) → (e1' : A' ≃ B) → Type (ℓ-suc ℓ)
  P A' e1' = pathAssoc (ua e1') (ua e2) (ua e3) i ≡ cong ua (compEquiv-assoc e1' e2 e3) i
  r : P B (idEquiv B)
  r = r2 e2 e3 i

uaAssocFunctoriality : ∀ {ℓ}{A B C D : Type ℓ} → (e1 : A ≃ B) → (e2 : B ≃ C) → (e3 : C ≃ D) → (i : I) →
    pathAssoc (ua e1) (ua e2) (ua e3) i ≡ cong ua (compEquiv-assoc e1 e2 e3) i
uaAssocFunctoriality = r1

-- aux1 : cong code (looping (m(g2 , g3))) ≡ ua (equivs (m(g2 , g3)))
-- aux1 =
--   cong (λ x → x ∙ cong code (looping g3)) (naturalityOfUaPaths g2) ∙
--   cong (λ x → (ua (equivs g2)) ∙ x) (naturalityOfUaPaths g3) ∙
--   sym (uaCompEquiv (equivs g2) (equivs g3)) ∙
--   cong ua (naturalityOfEquivs g2 g3) ∙ refl
-- aux2 : cong code (looping (m(g1 , g2))) ≡ ua (equivs (m(g1 , g2)))
-- aux2 =
--   cong (λ x → x ∙ cong code (looping g2)) (naturalityOfUaPaths g1) ∙
--   cong (λ x → (ua (equivs g1)) ∙ x) (naturalityOfUaPaths g2) ∙
--   sym (uaCompEquiv (equivs g1) (equivs g2)) ∙
--   cong ua (naturalityOfEquivs g1 g2) ∙ refl
-- l0  : cong code (looping (m(g1 , m(g2 , g3)))) ≡ ua (equivs (m(g1 , m(g2 , g3))))
-- l0 = naturalityOfUaPaths (m(g1 , m(g2 , g3)))
-- l1 : cong code (looping (m(m(g1 , g2) , g3))) ≡ ua (equivs (m(m(g1 , g2) , g3)))
-- l1 = naturalityOfUaPaths (m(m(g1 , g2) , g3))
-- a₀₀ = cong code (looping (m(g1 , m(g2 , g3))))
-- a₀₁ = ua (equivs (m(g1 , m(g2 , g3))))
-- a₁₀ = cong code (looping (m(m(g1 , g2) , g3)))
-- a₁₁ = ua (equivs (m(m(g1 , g2) , g3)))
-- a₀₋ : a₀₀ ≡ a₀₁
-- a₀₋ = l0
-- a₁₋ : a₁₀ ≡ a₁₁
-- a₁₋ = l1
-- a₋₀ : a₀₀ ≡ a₁₀
-- a₋₀ = λ i → cong code (looping (assoc g1 g2 g3 i))
-- a₋₁ : a₀₁ ≡ a₁₁
-- a₋₁ = λ i → ua (equivs (assoc g1 g2 g3 i))
-- square = Square a₀₋ a₁₋ a₋₀ a₋₁
-- -- postulate s : square
-- -- postulate p : PathP (λ i → cong code (looping (assoc g1 g2 g3 i)) ≡ ua (equivs (assoc g1 g2 g3 i))) l0 l1
-- -- cong code (looping (m(g1 , m(g2 , g3)))) ----------- l0/a₀₋ -----------→ ua (equivs (m(g1 , m(g2 , g3))))
-- --         |                                                                            |
-- --         a₋₀                                                                          a₋₁
-- --         ↓                                                                            ↓
-- -- cong code (looping (m(m(g1 , g2) , g3))) ----------- l1/a₁₋ -----------→ ua (equivs (m(m(g1 , g2) , g3)))
-- v1 : ua (equivs g1) ∙ cong code (looping (m(g2 , g3))) ≡ ua (equivs (m(g1 , g2))) ∙ cong code (looping g3)
-- v1 =
--   ua (equivs g1) ∙ cong code (looping (m(g2 , g3)))
--   ≡⟨ cong (λ s → ua (equivs g1) ∙ s) aux1 ⟩
--   ua (equivs g1) ∙ ua (equivs (m(g2 , g3)))
--   ≡⟨ sym (uaCompEquiv (equivs g1) (equivs (m(g2 , g3)))) ⟩
--   ua (compEquiv (equivs g1) (equivs (m(g2 , g3))))
--   ≡⟨ cong ua (naturalityOfEquivs g1 (m(g2 , g3))) ⟩
--   ua (equivs (m(g1 , m(g2 , g3))))
--   ≡⟨ cong (λ x → ua (equivs x)) (assoc g1 g2 g3) ⟩
--   ua (equivs (m(m (g1 , g2) , g3)))
--   ≡⟨ cong ua (sym (naturalityOfEquivs (m (g1 , g2)) g3)) ⟩
--   ua (compEquiv (equivs (m (g1 , g2))) (equivs g3))
--   ≡⟨ uaCompEquiv (equivs (m (g1 , g2))) (equivs g3) ⟩
--   ua (equivs (m (g1 , g2))) ∙ ua (equivs g3)
--   ≡⟨ cong (λ s → ua (equivs (m (g1 , g2))) ∙ s) (sym (naturalityOfUaPaths g3)) ⟩
--   ua (equivs (m(g1 , g2))) ∙ cong code (looping g3) ∎
-- v2 : ua (equivs g1) ∙ ua (equivs (m(g2 , g3))) ≡ ua (equivs (m(g1 , g2))) ∙ ua (equivs g3)
-- v2 =
--   ua (equivs g1) ∙ ua (equivs (m(g2 , g3)))
--   ≡⟨ sym (uaCompEquiv (equivs g1) (equivs (m(g2 , g3)))) ⟩
--   ua (compEquiv (equivs g1) (equivs (m(g2 , g3))))
--   ≡⟨ cong ua (naturalityOfEquivs g1 (m(g2 , g3))) ⟩
--   ua (equivs (m(g1 , m(g2 , g3))))
--   ≡⟨ cong (λ x → ua (equivs x)) (assoc g1 g2 g3) ⟩
--   ua (equivs (m(m(g1 , g2) , g3)))
--   ≡⟨ cong ua (sym (naturalityOfEquivs (m(g1 , g2)) g3)) ⟩
--   ua (compEquiv (equivs (m(g1 , g2))) (equivs g3) )
--   ≡⟨ uaCompEquiv (equivs (m(g1 , g2))) (equivs g3) ⟩
--   ua (equivs (m(g1 , g2))) ∙ ua (equivs g3) ∎
-- v3 : ua (compEquiv (equivs g1) (equivs (m(g2 , g3)))) ≡ ua (compEquiv (equivs (m(g1 , g2))) (equivs g3))
-- v3 =
--   ua (compEquiv (equivs g1) (equivs (m(g2 , g3))))
--   ≡⟨ cong ua (naturalityOfEquivs g1 (m(g2 , g3))) ⟩
--   ua (equivs (m(g1 , m(g2 , g3))))
--   ≡⟨ cong (λ x → ua (equivs x)) (assoc g1 g2 g3) ⟩
--   ua (equivs (m(m(g1 , g2) , g3)))
--   ≡⟨ cong ua (sym (naturalityOfEquivs (m(g1 , g2)) g3)) ⟩
--   ua (compEquiv (equivs (m(g1 , g2))) (equivs g3)) ∎
-- postulate s1 : PathP (λ i → cong code (looping (assoc g1 g2 g3 i)) ≡ v1 i) (cong (λ x → x ∙ cong code (looping (m(g2 , g3)))) (naturalityOfUaPaths g1)) (cong (λ x → x ∙ cong code (looping g3)) (aux2))
-- postulate s2 : PathP (λ i → v1 i ≡ v2 i) (cong (λ x → (ua (equivs g1)) ∙ x) (aux1)) (cong (λ x → (ua (equivs (m(g1 , g2)))) ∙ x) (naturalityOfUaPaths g3))
-- postulate s3 : PathP (λ i → v2 i ≡ v3 i) (sym (uaCompEquiv (equivs g1) (equivs (m(g2 , g3))))) (sym (uaCompEquiv (equivs (m(g1 , g2))) (equivs g3)))
-- postulate s4 : PathP (λ i → v3 i ≡ ua (equivs (assoc g1 g2 g3 i))) (cong ua (naturalityOfEquivs g1 (m(g2 , g3)))) (cong ua (naturalityOfEquivs (m(g1 , g2)) g3))
-- -- s4 = λ i →
-- -- ua (compEquiv (equivs g1) (equivs (m(g2 , g3)))) --- ua (compEquiv (equivs g1) (compEquiv (equivs g2) (equivs g3))) --- l0 ----- ua (equivs g1 * (g2 * g3))
-- --     |                                                  |                                                                          |
-- --     |v3 i                                              | ua(compEquiv-assoc (equivs g1) (equivs g2) (equivs g3) i)                |ua (equivs (assoc g1 g2 g3 i)))
-- --     |                                                  |                                                                          |
-- -- ua (compEquiv (equivs (m(g1 , g2))) (equivs g3)) --- ua (compEquiv (compEquiv (equivs g1) (equivs g2)) (equivs g3)) --- l1 ----- ua (equivs (g1 * g2) * g3)
-- s5 : PathP (λ i → ua (equivs (assoc g1 g2 g3 i)) ≡ ua (equivs (assoc g1 g2 g3 i))) refl refl
-- s5 = λ i → refl
-- s : square
-- s = compSquares s1 (compSquares s2 (compSquares s3 (compSquares s4 s5)))
