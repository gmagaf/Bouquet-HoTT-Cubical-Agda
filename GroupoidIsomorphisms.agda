{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)

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
    ≡⟨ sym (idr g) ⟩
    g
    ≡⟨ refl ⟩
    idfun (FreeGroupoid A) g ∎

invAutomorhpism :  FreeGroupoid A → FreeGroupoid A → FreeGroupoid A
invAutomorhpism a = automorhpism (inv a)
rhomotopy : ∀ (a : FreeGroupoid A) → ∀ (g : FreeGroupoid A) → (automorhpism a) (invAutomorhpism a g) ≡ g
rhomotopy a g =
  (automorhpism a) (invAutomorhpism a g)
  ≡⟨ refl ⟩
  m(m(g , inv a) , a)
  ≡⟨ sym (assoc g (inv a) a) ⟩
  m(g , m(inv a , a))
  ≡⟨ cong (λ x → m(g , x)) (invl a) ⟩
  m(g , e)
  ≡⟨ sym (idr g) ⟩
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
  ≡⟨ sym (idr g) ⟩
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

naturalityOfAssocEquivs : ∀ {ℓ}{A : Type ℓ} → (g1 g2 g3 : FreeGroupoid A) → (i : I) →
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
    automorhpism (m(g2 , g3)) ∘ (automorhpism g1)
    ≡⟨ multNaturality g1 (m(g2 , g3)) ⟩
    automorhpism (m(g1 , m(g2 , g3)))
    ≡⟨ cong automorhpism (λ j → assoc g1 g2 g3 (j ∧ i)) ⟩
    automorhpism (assoc g1 g2 g3 i)
    ≡⟨ refl ⟩
    equivs (assoc g1 g2 g3 i) .fst ∎

-- Some other implementations of pathsInU

automorhpism' : ∀ (a : A) → FreeGroupoid A → FreeGroupoid A
automorhpism' a g = m(g , η a)

invAutomorhpism' :  ∀ (a : A) → FreeGroupoid A → FreeGroupoid A
invAutomorhpism' a g = m(g , inv(η a))

rhomotopy' : ∀ (a : A) → ∀ (g : FreeGroupoid A) → (automorhpism' a) (invAutomorhpism' a g) ≡ g
rhomotopy' a g =
  (automorhpism' a) (invAutomorhpism' a g)
  ≡⟨ refl ⟩
  m(m(g , inv (η a)) , (η a))
  ≡⟨ sym (assoc g (inv (η a)) (η a)) ⟩
  m(g , m(inv (η a) , (η a)))
  ≡⟨ cong (λ x → m(g , x)) (invl (η a)) ⟩
  m(g , e)
  ≡⟨ sym (idr g) ⟩
  g ∎
lhomotopy' : ∀ (a : A) → ∀ (g : FreeGroupoid A) → invAutomorhpism' a ((automorhpism' a) g) ≡ g
lhomotopy' a g =
  invAutomorhpism' a ((automorhpism' a) g)
  ≡⟨ refl ⟩
  m(m(g , (η a)) , inv (η a))
  ≡⟨ sym (assoc g (η a) (inv (η a))) ⟩
  m(g , m((η a) , inv (η a)))
  ≡⟨ cong (λ x → m(g , x)) (invr (η a)) ⟩
  m(g , e)
  ≡⟨ sym (idr g) ⟩
  g ∎

biInvAutomorphisms' : A → BiInvEquiv (FreeGroupoid A) (FreeGroupoid A)
biInvAutomorphisms' a = biInvEquiv (automorhpism' a) (invAutomorhpism' a) (rhomotopy' a) (invAutomorhpism' a) (lhomotopy' a)

equivAutomorphisms' : A → (FreeGroupoid A) ≃ (FreeGroupoid A)
equivAutomorphisms' a = biInvEquiv→Equiv-right (biInvAutomorphisms' a)

pathsInU' : FreeGroupoid A → (FreeGroupoid A) ≡ (FreeGroupoid A)
pathsInU' (η a)              = ua (equivAutomorphisms' a)
pathsInU' (m(g1 , g2))       = pathsInU' g1 ∙ pathsInU' g2
pathsInU' e                  = refl
pathsInU' (inv g)            = sym (pathsInU' g)
pathsInU' (assoc g1 g2 g3 i) = pathAssoc (pathsInU' g1) (pathsInU' g2) (pathsInU' g3) i
pathsInU' (idr g i)          = rUnit (pathsInU' g) i
pathsInU' (idl g i)          = lUnit (pathsInU' g) i
pathsInU' (invr g i)         = rCancel (pathsInU' g) i
pathsInU' (invl g i)         = lCancel (pathsInU' g) i

equivs'' : FreeGroupoid A → (FreeGroupoid A) ≃ (FreeGroupoid A)
equivs'' (η a)              = equivAutomorphisms' a
equivs'' (m(g1 , g2))       = compEquiv (equivs'' g1) (equivs'' g2)
equivs'' e                  = idEquiv _
equivs'' (inv g)            = invEquiv (equivs'' g)
equivs'' (assoc g1 g2 g3 i) = compEquiv-assoc (equivs'' g1) (equivs'' g2) (equivs'' g3) i
equivs'' (idr g i)          = sym (compEquivEquivId (equivs'' g)) i
equivs'' (idl g i)          = sym (compEquivIdEquiv (equivs'' g)) i
equivs'' (invr g i)         = invEquiv-is-rinv (equivs'' g) i
equivs'' (invl g i)         = invEquiv-is-linv (equivs'' g) i

pathsInU'' : FreeGroupoid A → (FreeGroupoid A) ≡ (FreeGroupoid A)
pathsInU'' g = ua (equivs'' g)
