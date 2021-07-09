{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Function

open import WA.WA
open import WA.FreeGroupoid

module WA.GroupoidIsomorphisms where

private
  variable
    ℓ : Level
    A : Type ℓ


automorhpism : ∀ (a : FreeGroupoid A) → FreeGroupoid A → FreeGroupoid A
automorhpism a g = m(g , a)

multNaturality : (g1 g2 : FreeGroupoid A) → (automorhpism g2 ∘ automorhpism g1) ≡ automorhpism (m(g1 , g2))
multNaturality g1 g2 = funExt (pointwise g1 g2) where
  pointwise : (g1 g2 g3 : FreeGroupoid A) → (automorhpism g2 ∘ automorhpism g1) g3 ≡ automorhpism (m(g1 , g2)) g3
  pointwise g1 g2 g3 =
    (automorhpism g2 ∘ automorhpism g1) g3
    ≡⟨ refl ⟩
    automorhpism g2 (automorhpism g1 g3)
    ≡⟨ refl ⟩
    automorhpism g2 (m(g3 , g1))
    ≡⟨ refl ⟩
    m(m(g3 , g1) , g2)
    ≡⟨ sym (assoc g3 g1 g2) ⟩
    m(g3 , m(g1 , g2))
    ≡⟨ refl ⟩
    automorhpism (m(g1 , g2)) g3 ∎

idNaturality : ∀ {ℓ}{A : Type ℓ} → automorhpism e ≡ idfun (FreeGroupoid A)
idNaturality {A = A} = funExt pointwise where
  pointwise : (g : FreeGroupoid A) → automorhpism e g ≡ idfun (FreeGroupoid A) g
  pointwise g =
    automorhpism e g
    ≡⟨ refl ⟩
    m(g , e)
    ≡⟨ idr g ⟩
    g
    ≡⟨ refl ⟩
    idfun (FreeGroupoid A) g ∎

invAutomorhpism :  FreeGroupoid A → FreeGroupoid A → FreeGroupoid A
invAutomorhpism a = automorhpism (inv a)
rhomotopy : ∀ (a : FreeGroupoid A) → ∀ (g : FreeGroupoid A) → (automorhpism a) (invAutomorhpism a g) ≡ g
rhomotopy a g = --sym (assoc g (inv a) a) ∙ cong (λ x → m(g , x)) (invl a) ∙ idr g
  (automorhpism a) (invAutomorhpism a g)
  ≡⟨ refl ⟩
  m(m(g , inv a) , a)
  ≡⟨ sym (assoc g (inv a) a) ⟩
  m(g , m(inv a , a))
  ≡⟨ cong (λ x → m(g , x)) (invl a) ⟩
  m(g , e)
  ≡⟨ idr g ⟩
  g ∎
lhomotopy : ∀ (a : FreeGroupoid A) → ∀ (g : FreeGroupoid A) → invAutomorhpism a ((automorhpism a) g) ≡ g
lhomotopy a g =
  invAutomorhpism a ((automorhpism a) g)
  ≡⟨ refl ⟩
  m(m(g , a) , inv a)
  ≡⟨ sym (assoc g a (inv a)) ⟩
  m(g , m(a , inv a))
  ≡⟨ cong (λ x → m(g , x)) (invr a) ⟩
  m(g , e)
  ≡⟨ idr g ⟩
  g ∎

biInvAutomorphisms : FreeGroupoid A → BiInvEquiv (FreeGroupoid A) (FreeGroupoid A)
biInvAutomorphisms a = biInvEquiv (automorhpism a) (invAutomorhpism a) (rhomotopy a) (invAutomorhpism a) (lhomotopy a)

equivs : FreeGroupoid A → (FreeGroupoid A) ≃ (FreeGroupoid A)
equivs a = biInvEquiv→Equiv-right (biInvAutomorphisms a)

pathsInU : FreeGroupoid A → (FreeGroupoid A) ≡ (FreeGroupoid A)
pathsInU a = ua (equivs a)

naturalityOfEquivs : ∀ (k1 k2 : FreeGroupoid A) → compEquiv (equivs k1) (equivs k2) ≡ equivs (m(k1 , k2))
naturalityOfEquivs k1 k2 = equivEq h where
  h : (compEquiv (equivs k1) (equivs k2)) .fst ≡ (equivs (m(k1 , k2))) .fst
  h =
    compEquiv (equivs k1) (equivs k2) .fst
    ≡⟨ refl ⟩
    ((equivs k2) .fst) ∘ ((equivs k1) .fst)
    ≡⟨ refl ⟩
    (automorhpism k2) ∘ ((equivs k1) .fst)
    ≡⟨ refl ⟩
    (automorhpism k2) ∘ (automorhpism k1)
    ≡⟨ multNaturality k1 k2 ⟩
    automorhpism (m(k1 , k2))
    ≡⟨ refl ⟩
    equivs (m(k1 , k2)) .fst ∎

naturalityOfIdEquivs : ∀ {ℓ}{A : Type ℓ} → idEquiv (FreeGroupoid A) ≡ equivs e
naturalityOfIdEquivs {A = A} = equivEq h where
  h : idEquiv (FreeGroupoid A) .fst ≡ (equivs e) .fst
  h =
    idEquiv (FreeGroupoid A) .fst
    ≡⟨ refl ⟩
    idfun (FreeGroupoid A)
    ≡⟨ sym idNaturality ⟩
    automorhpism e
    ≡⟨ refl ⟩
    (equivs e) .fst ∎

naturalityOfInvEquivs : ∀ {ℓ}{A : Type ℓ} → (g : FreeGroupoid A) → invEquiv (equivs g) ≡ equivs (inv g)
naturalityOfInvEquivs g = equivEq h where
  h : invEquiv (equivs g) .fst ≡ (equivs (inv g)) .fst
  h =
    invEquiv (equivs g) .fst
    ≡⟨ refl ⟩
    invAutomorhpism g
    ≡⟨ refl ⟩
    automorhpism (inv g)
    ≡⟨ refl ⟩
    (equivs (inv g)) .fst ∎
