{-

This file contains:

- Natural functions from FreeGroupoid into FreeGroupoid
- Proofs that they induce equivalences
- Natural paths in Universe from FreeGroupoid to FreeGroupoid
- Proofs that these functions and paths respect the groupoid structure of FreeGroupoid

-}
{-# OPTIONS --cubical #-}

module WA.FreeGroupoid.Automorhpisms where

open import WA.FreeGroupoid.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Function

private
  variable
    ℓ : Level
    A : Type ℓ

automorhpism : ∀ (a : FreeGroupoid A) → FreeGroupoid A → FreeGroupoid A
automorhpism a g = m g a

invAutomorhpism :  FreeGroupoid A → FreeGroupoid A → FreeGroupoid A
invAutomorhpism a = automorhpism (inv a)

multNaturality : (g1 g2 : FreeGroupoid A) → automorhpism (m g1 g2) ≡ (automorhpism g2 ∘ automorhpism g1)
multNaturality g1 g2 = funExt (pointwise g1 g2) where
  pointwise : (g1 g2 g3 : FreeGroupoid A) → automorhpism (m g1 g2) g3 ≡ (automorhpism g2 ∘ automorhpism g1) g3
  pointwise g1 g2 g3 =
    automorhpism (m g1 g2) g3
    ≡⟨ refl ⟩
    m g3 (m g1 g2)
    ≡⟨ assoc g3 g1 g2 ⟩
    m (m g3 g1) g2
    ≡⟨ refl ⟩
    automorhpism g2 (m g3 g1)
    ≡⟨ refl ⟩
    automorhpism g2 (automorhpism g1 g3)
    ≡⟨ refl ⟩
    (automorhpism g2 ∘ automorhpism g1) g3 ∎

idNaturality : automorhpism e ≡ idfun (FreeGroupoid A)
idNaturality = funExt pointwise where
  pointwise : (g : FreeGroupoid A) → automorhpism e g ≡ idfun (FreeGroupoid A) g
  pointwise g =
    automorhpism e g
    ≡⟨ refl ⟩
    m g e
    ≡⟨ sym (idr g) ⟩
    g
    ≡⟨ refl ⟩
    idfun _ g ∎

assocAutomorphisms : ∀ (a1 a2 a3 : FreeGroupoid A)
  → automorhpism a1 ∘ (automorhpism a2 ∘ automorhpism a3) ≡ (automorhpism a1 ∘ automorhpism a2) ∘ automorhpism a3
assocAutomorphisms a1 a2 a3 = refl

rUnitAutomorphisms : ∀ (a : FreeGroupoid A) → automorhpism a ≡ automorhpism a ∘ idfun (FreeGroupoid A)
rUnitAutomorphisms a = refl

lUnitAutomorphisms : ∀ (a : FreeGroupoid A) → automorhpism a ≡ idfun (FreeGroupoid A) ∘ automorhpism a
lUnitAutomorphisms a = refl

rCancelAutomorphisms : ∀ (a : FreeGroupoid A) → automorhpism a ∘ invAutomorhpism a ≡ idfun (FreeGroupoid A)
rCancelAutomorphisms a =
  automorhpism a ∘ invAutomorhpism a
  ≡⟨ sym (multNaturality (inv a) a) ⟩
  automorhpism (m (inv a) a)
  ≡⟨ cong automorhpism (invl a) ⟩
  automorhpism e
  ≡⟨ idNaturality ⟩
  idfun _ ∎

lCancelAutomorphisms : ∀ (a : FreeGroupoid A) → invAutomorhpism a ∘ automorhpism a ≡ idfun (FreeGroupoid A)
lCancelAutomorphisms a =
  invAutomorhpism a ∘ automorhpism a
  ≡⟨ sym (multNaturality a (inv a)) ⟩
  automorhpism (m a (inv a))
  ≡⟨ cong automorhpism (invr a) ⟩
  automorhpism e
  ≡⟨ idNaturality ⟩
  idfun _ ∎

epi : ∀ (f : FreeGroupoid A → FreeGroupoid A)
      → (∀ g1 g2 → f (m g1 g2) ≡ m g1 (f g2))
      → Σ[ a ∈ FreeGroupoid A ] (f ≡ automorhpism a)
epi f property = f e , (funExt pointwise) where
  pointwise : ∀ g → f g ≡ automorhpism (f e) g
  pointwise g =
    f g
    ≡⟨ cong f (idr g) ⟩
    f (m g e)
    ≡⟨ property g e ⟩
    automorhpism (f e) g ∎


biInvAutomorphisms : FreeGroupoid A → BiInvEquiv (FreeGroupoid A) (FreeGroupoid A)
biInvAutomorphisms a = biInvEquiv (automorhpism a) (invAutomorhpism a) (rhomotopy a) (invAutomorhpism a) (lhomotopy a) where
  rhomotopy : ∀ a g → (automorhpism a ∘ invAutomorhpism a) g ≡ g
  rhomotopy a g = cong (λ f → f g) (rCancelAutomorphisms a)
  lhomotopy : ∀ a g → (invAutomorhpism a ∘ automorhpism a) g ≡ g
  lhomotopy a g = cong (λ f → f g) (lCancelAutomorphisms a)

equivs : FreeGroupoid A → (FreeGroupoid A) ≃ (FreeGroupoid A)
equivs a = biInvEquiv→Equiv-right (biInvAutomorphisms a)

multEquivsNaturality : ∀ (k1 k2 : FreeGroupoid A) → equivs (m k1 k2) ≡ compEquiv (equivs k1) (equivs k2)
multEquivsNaturality k1 k2 = equivEq h where
  h : (equivs (m k1 k2)) .fst ≡ (compEquiv (equivs k1) (equivs k2)) .fst
  h =
    equivs (m k1 k2) .fst
    ≡⟨ refl ⟩
    automorhpism (m k1 k2)
    ≡⟨ multNaturality k1 k2 ⟩
    (automorhpism k2) ∘ (automorhpism k1)
    ≡⟨ refl ⟩
    ((equivs k2) .fst) ∘ ((equivs k1) .fst)
    ≡⟨ refl ⟩
    compEquiv (equivs k1) (equivs k2) .fst ∎

idEquivsNaturality : equivs e ≡ idEquiv (FreeGroupoid A)
idEquivsNaturality = equivEq h where
  h : (equivs e) .fst ≡ idEquiv (FreeGroupoid A) .fst
  h =
    (equivs e) .fst
    ≡⟨ refl ⟩
    automorhpism e
    ≡⟨ idNaturality ⟩
    idfun _
    ≡⟨ refl ⟩
    idEquiv _ .fst ∎

invEquivsNaturality : ∀ (g : FreeGroupoid A) → equivs (inv g) ≡ invEquiv (equivs g)
invEquivsNaturality g = equivEq refl


pathsInU : {A : Type ℓ} → FreeGroupoid A → (FreeGroupoid A) ≡ (FreeGroupoid A)
pathsInU a = ua (equivs a)

multPathsInUNaturality : ∀ (g1 g2 : FreeGroupoid A) → pathsInU (m g1 g2) ≡ (pathsInU g1) ∙ (pathsInU g2)
multPathsInUNaturality g1 g2 =
  pathsInU (m g1 g2)
  ≡⟨ refl ⟩
  ua (equivs (m g1 g2))
  ≡⟨ cong ua (multEquivsNaturality g1 g2) ⟩
  ua (compEquiv (equivs g1) (equivs g2))
  ≡⟨ uaCompEquiv (equivs g1) (equivs g2) ⟩
  (pathsInU g1) ∙ (pathsInU g2) ∎

idPathsInUNaturality : pathsInU {A = A} e ≡ refl
idPathsInUNaturality =
  pathsInU e
  ≡⟨ refl ⟩
  ua (equivs e)
  ≡⟨ cong ua idEquivsNaturality ⟩
  ua (idEquiv _)
  ≡⟨ uaIdEquiv ⟩
  refl ∎

invPathsInUNaturality : ∀ (g : FreeGroupoid A) → pathsInU (inv g) ≡ sym (pathsInU g)
invPathsInUNaturality g =
  pathsInU (inv g)
  ≡⟨ refl ⟩
  ua (equivs (inv g))
  ≡⟨ cong ua (invEquivsNaturality g) ⟩
  ua (invEquiv (equivs g))
  ≡⟨ uaInvEquiv (equivs g) ⟩
  sym (pathsInU g) ∎
