{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

open import WA.WA
open import WA.FreeGroupoid

module WA.GroupoidIsomorphisms where

private
  variable
    ℓ : Level
    A : Type ℓ


automorhpism : A → FreeGroupoid A → FreeGroupoid A
automorhpism a g = m(g , η a)

isomorphisms : A → Iso (FreeGroupoid A) (FreeGroupoid A)
isomorphisms a = record {
  fun = automorhpism a ;
  inv = invfun a ;
  rightInv = rhomotopy a ;
  leftInv = lhomotopy a} where
  invfun : A → FreeGroupoid A → FreeGroupoid A
  invfun a g = m(g , inv (η a))
  rhomotopy : ∀ (a : A) → ∀ (g : FreeGroupoid A) → (automorhpism a) (invfun a g) ≡ g
  rhomotopy a g =
    (automorhpism a) (invfun a g)
    ≡⟨ refl ⟩
    m(m(g , inv (η a)) , η a)
    ≡⟨ sym (assoc g (inv (η a)) (η a)) ⟩
    m(g , m(inv (η a) , η a))
    ≡⟨ cong (λ x → m(g , x)) (invl (η a)) ⟩
    m(g , e)
    ≡⟨ idr g ⟩
    g ∎
  lhomotopy : ∀ (a : A) → ∀ (g : FreeGroupoid A) → invfun a ((automorhpism a) g) ≡ g
  lhomotopy a g =
    invfun a ((automorhpism a) g)
    ≡⟨ refl ⟩
    m(m(g , η a) , inv (η a))
    ≡⟨ sym (assoc g (η a) (inv (η a))) ⟩
    m(g , m(η a , inv(η a)))
    ≡⟨ cong (λ x → m(g , x)) (invr (η a)) ⟩
    m(g , e)
    ≡⟨ idr g ⟩
    g ∎

equivs : A → (FreeGroupoid A) ≃ (FreeGroupoid A)
equivs a = isoToEquiv (isomorphisms a)

pathsInU : A → (FreeGroupoid A) ≡ (FreeGroupoid A)
pathsInU a = ua (equivs a)

fiberY : ∀ (a : A) → ∀ (y : FreeGroupoid A) → (fiber (automorhpism a) y)
fiberY a y = (m(y , inv (η a)) , eq) where
  eq : (automorhpism a) (m(y , inv (η a))) ≡ y
  eq =
    (automorhpism a) (m(y , inv (η a)))
    ≡⟨ refl ⟩
    m(m(y , inv (η a)) , η a)
    ≡⟨ sym (assoc y (inv (η a)) (η a)) ⟩
    m(y , m(inv (η a) , η a))
    ≡⟨ cong (λ x → m(y , x)) (invl (η a)) ⟩
    m(y , e)
    ≡⟨ idr y ⟩
    y ∎

-- fiberYisContr : ∀ (a : A) → ∀ (y : FreeGroupoid A) → isContr (fiber (automorhpism a) y)
-- fiberYisContr a y = (fiberY a y , unique) where
--   x : FreeGroupoid A
--   x = fst (fiberY a y)
--   eq : automorhpism a x ≡ y
--   eq = snd (fiberY a y)
--   unique : ∀ z → (x , eq) ≡ z
--   unique (x' , eq') = (xs , eqs) where
--     xs : x ≡ x'
--     xs =
--       x
--       ≡⟨ refl ⟩
--       m(y , inv (η a))
--       ≡⟨ cong (λ z → m(z , inv (η a))) (sym eq') ⟩
--       m(automorhpism a x' , inv (η a))
--       ≡⟨ refl ⟩
--       m(m(x' , η a) , inv (η a))
--       ≡⟨ assoc x' (η a) (inv (η a)) ⟩
--       m(x' , m(η a , inv (η a)))
--       ≡⟨ cong (λ z → m(x' , z)) (invr (η a)) ⟩
--       m(x' , e)
--       ≡⟨ idr x' ⟩
--       x' ∎
--     eqs : eq ≡ eq'
--     eqs = cong () xs
-- automorhpismIsEquiv : A → isEquiv (automorhpism a)
-- equiv-proof (automorhpismIsEquiv a) y =
