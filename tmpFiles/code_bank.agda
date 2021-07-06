{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Function

open import WA.WA
open import WA.FreeGroupoid
open import WA.GroupoidIsomorphisms

module WA.tmpFiles.code_bank where

private
  variable
    ℓ : Level
    A : Type ℓ


fiberY : ∀ (a : FreeGroupoid A) → ∀ (y : FreeGroupoid A) → (fiber (automorhpism a) y)
fiberY a y = (m(y , inv a) , eq) where
  eq : (automorhpism a) (m(y , inv  a)) ≡ y
  eq =
    (automorhpism a) (m(y , inv a))
    ≡⟨ refl ⟩
    m(m(y , inv a) , a)
    ≡⟨ sym (assoc y (inv a) a) ⟩
    m(y , m(inv a , a))
    ≡⟨ cong (λ x → m(y , x)) (invl a) ⟩
    m(y , e)
    ≡⟨ idr y ⟩
    y ∎

-- fiberYisContr : ∀ (a : FreeGroupoid A) → ∀ (y : FreeGroupoid A) → isContr (fiber (automorhpism a) y)
-- fiberYisContr a y = (fiberY a y , unique) where
--   -- x : FreeGroupoid A
--   x = fst (fiberY a y)
--   eq : automorhpism a x ≡ y
--   eq = snd (fiberY a y)
--   unique : ∀ z → (x , eq) ≡ z
--   unique (x' , eq') = (xs , eqs) where
--     xs : x ≡ x'
--     xs =
--       x
--       ≡⟨ refl ⟩
--       m(y , inv a)
--       ≡⟨ cong (λ z → m(z , inv a)) (sym eq') ⟩
--       m(automorhpism a x' , inv a)
--       ≡⟨ refl ⟩
--       m(m(x' , a) , inv a)
--       ≡⟨ sym (assoc x' a (inv a)) ⟩
--       m(x' , m(a , inv a))
--       ≡⟨ cong (λ z → m(x' , z)) (invr a) ⟩
--       m(x' , e)
--       ≡⟨ idr x' ⟩
--       x' ∎
--     eqs : PathP (λ i → automorhpism a (xs i) ≡ y) eq eq'
--     eqs = λ i → (cong (automorhpism a) xs) i ≡ y

-- automorhpismIsEquiv : A → isEquiv (automorhpism a)
-- equiv-proof (automorhpismIsEquiv a) y =

biInvComp : (X Y Z : Type) → BiInvEquiv X Y → BiInvEquiv Y Z → BiInvEquiv X Z
biInvComp X Y Z (biInvEquiv f1 g1 r1 h1 l1) (biInvEquiv f2 g2 r2 h2 l2) = biInvEquiv f g α h β where
  f : X → Z
  f x = f2 (f1 x)
  g : Z → X
  g z = g1 (g2 z)
  α : ∀ z → f (g z) ≡ z
  α z = (cong f2 (r1 (g2 z))) ∙ (r2 z)
  h : Z → X
  h z = h1 (h2 z)
  β : ∀ x → h (f x) ≡ x
  β x = (cong h1 (l2 (f1 x))) ∙ (l1 x)
