{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)

open import WA.FreeGroup

module WA.GroupIsomorphisms where

private
  variable
    ℓ : Level
    A : Type ℓ


automorhpism : ∀ (a : FreeGroup A) → FreeGroup A → FreeGroup A
automorhpism a g = m g a

multNaturality : (g1 g2 : FreeGroup A) → (automorhpism g2 ∘ automorhpism g1) ≡ automorhpism (m g1 g2)
multNaturality g1 g2 = funExt (pointwise g1 g2) where
  pointwise : (g1 g2 g3 : FreeGroup A) → (automorhpism g2 ∘ automorhpism g1) g3 ≡ automorhpism (m g1 g2) g3
  pointwise g1 g2 g3 =
    (automorhpism g2 ∘ automorhpism g1) g3
    ≡⟨ refl ⟩
    automorhpism g2 (automorhpism g1 g3)
    ≡⟨ refl ⟩
    automorhpism g2 (m g3 g1)
    ≡⟨ refl ⟩
    m (m g3 g1) g2
    ≡⟨ sym (assoc g3 g1 g2) ⟩
    m g3 (m g1 g2)
    ≡⟨ refl ⟩
    automorhpism (m g1 g2) g3 ∎

idNaturality : ∀ {ℓ}{A : Type ℓ} → automorhpism e ≡ idfun (FreeGroup A)
idNaturality {A = A} = funExt pointwise where
  pointwise : (g : FreeGroup A) → automorhpism e g ≡ idfun (FreeGroup A) g
  pointwise g =
    automorhpism e g
    ≡⟨ refl ⟩
    m g e
    ≡⟨ sym (idr g) ⟩
    g
    ≡⟨ refl ⟩
    idfun (FreeGroup A) g ∎

invAutomorhpism :  FreeGroup A → FreeGroup A → FreeGroup A
invAutomorhpism a = automorhpism (inv a)
rhomotopy : ∀ (a : FreeGroup A) → ∀ (g : FreeGroup A) → (automorhpism a) (invAutomorhpism a g) ≡ g
rhomotopy a g =
  (automorhpism a) (invAutomorhpism a g)
  ≡⟨ refl ⟩
  m (m g (inv a)) a
  ≡⟨ sym (assoc g (inv a) a) ⟩
  m g (m (inv a) a)
  ≡⟨ cong (λ x → m g x) (invl a) ⟩
  m g e
  ≡⟨ sym (idr g) ⟩
  g ∎
lhomotopy : ∀ (a : FreeGroup A) → ∀ (g : FreeGroup A) → invAutomorhpism a ((automorhpism a) g) ≡ g
lhomotopy a g =
  invAutomorhpism a ((automorhpism a) g)
  ≡⟨ refl ⟩
  m (m g a) (inv a)
  ≡⟨ sym (assoc g a (inv a)) ⟩
  m g (m a (inv a))
  ≡⟨ cong (λ x → m g x) (invr a) ⟩
  m g e
  ≡⟨ sym (idr g) ⟩
  g ∎

biInvAutomorphisms : FreeGroup A → BiInvEquiv (FreeGroup A) (FreeGroup A)
biInvAutomorphisms a = biInvEquiv (automorhpism a) (invAutomorhpism a) (rhomotopy a) (invAutomorhpism a) (lhomotopy a)

equivs : FreeGroup A → (FreeGroup A) ≃ (FreeGroup A)
equivs a = biInvEquiv→Equiv-right (biInvAutomorphisms a)

pathsInU : FreeGroup A → (FreeGroup A) ≡ (FreeGroup A)
pathsInU a = ua (equivs a)

naturalityOfEquivs : ∀ (k1 k2 : FreeGroup A) → compEquiv (equivs k1) (equivs k2) ≡ equivs (m k1 k2)
naturalityOfEquivs k1 k2 = equivEq h where
  h : (compEquiv (equivs k1) (equivs k2)) .fst ≡ (equivs (m k1 k2)) .fst
  h =
    compEquiv (equivs k1) (equivs k2) .fst
    ≡⟨ refl ⟩
    ((equivs k2) .fst) ∘ ((equivs k1) .fst)
    ≡⟨ refl ⟩
    (automorhpism k2) ∘ ((equivs k1) .fst)
    ≡⟨ refl ⟩
    (automorhpism k2) ∘ (automorhpism k1)
    ≡⟨ multNaturality k1 k2 ⟩
    automorhpism (m k1 k2)
    ≡⟨ refl ⟩
    equivs (m k1 k2) .fst ∎

naturalityOfIdEquivs : ∀ {ℓ}{A : Type ℓ} → idEquiv (FreeGroup A) ≡ equivs e
naturalityOfIdEquivs {A = A} = equivEq h where
  h : idEquiv (FreeGroup A) .fst ≡ (equivs e) .fst
  h =
    idEquiv (FreeGroup A) .fst
    ≡⟨ refl ⟩
    idfun (FreeGroup A)
    ≡⟨ sym idNaturality ⟩
    automorhpism e
    ≡⟨ refl ⟩
    (equivs e) .fst ∎

naturalityOfInvEquivs : ∀ {ℓ}{A : Type ℓ} → (g : FreeGroup A) → invEquiv (equivs g) ≡ equivs (inv g)
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

naturalityOfAssocEquivs : ∀ {ℓ}{A : Type ℓ} → (g1 g2 g3 : FreeGroup A) → (i : I) →
  compEquiv-assoc (equivs g1) (equivs g2) (equivs g3) i ≡ equivs (assoc g1 g2 g3 i)
naturalityOfAssocEquivs g1 g2 g3 i = equivEq h where
  h : compEquiv-assoc (equivs g1) (equivs g2) (equivs g3) i .fst ≡ equivs (assoc g1 g2 g3 i) .fst
  h =
    compEquiv-assoc (equivs g1) (equivs g2) (equivs g3) i .fst
    ≡⟨ refl ⟩
    (equivs g3) .fst ∘ (equivs g2) .fst ∘ (equivs g1) .fst
    ≡⟨ refl ⟩
    (automorhpism g3) ∘ (equivs g2) .fst ∘ (equivs g1) .fst
    ≡⟨ refl ⟩
    (automorhpism g3) ∘ (automorhpism g2) ∘ (equivs g1) .fst
    ≡⟨ refl ⟩
    (automorhpism g3) ∘ (automorhpism g2) ∘ (automorhpism g1)
    ≡⟨ cong (λ s → s ∘ (automorhpism g1)) (multNaturality g2 g3) ⟩
    automorhpism (m g2 g3) ∘ (automorhpism g1)
    ≡⟨ multNaturality g1 (m g2 g3) ⟩
    automorhpism (m g1 (m g2 g3))
    ≡⟨ cong automorhpism (λ j → assoc g1 g2 g3 (j ∧ i)) ⟩
    automorhpism (assoc g1 g2 g3 i)
    ≡⟨ refl ⟩
    equivs (assoc g1 g2 g3 i) .fst ∎
