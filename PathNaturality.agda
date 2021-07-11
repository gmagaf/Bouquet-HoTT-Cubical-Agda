{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

module WA.PathNaturality where

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
  uaAssocFunctoriality : ∀ {ℓ}{A B C D : Type ℓ} → (e1 : A ≃ B) → (e2 : B ≃ C) → (e3 : C ≃ D) → uaAssocSquare e1 e2 e3
