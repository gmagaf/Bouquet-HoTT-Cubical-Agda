{-

This file contains:

- Proof that the fundamental group of a type is indeed a group

-}
{-# OPTIONS --cubical #-}

module WA.FundamentalGroup.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.SetTruncation
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base

open import WA.FundamentalGroup.Base

private
  variable
    ℓ : Level
    A : Type ℓ
    base : A

-- Some Properties of the fundamental group

π₁IsSet : isSet (π₁ {base = base})
π₁IsSet = squash₂

≡π₁IsProp : ∀ (r s : π₁ {base = base}) → isProp (r ≡ s)
≡π₁IsProp r s = squash₂ r s

≡π₁IsSet : ∀ (r s : π₁ {base = base}) → isSet (r ≡ s)
≡π₁IsSet r s = isProp→isSet (≡π₁IsProp r s)

1π₁ : π₁ {base = base}
1π₁ = ∣ refl ∣₂

invπ₁ : π₁ {base = base} → π₁
invπ₁ r = rec π₁IsSet symLoopClass r where
  symLoopClass : Ω → π₁
  symLoopClass p = ∣ sym p ∣₂

∙-π₁ : π₁ {base = base} → π₁ → π₁
∙-π₁ r s = rec π₁IsSet sndRec s where
  sndRec : Ω → π₁
  sndRec q = rec π₁IsSet (λ p → ∣ p ∙ q ∣₂) r

assocπ₁ : ∀ (r s t : π₁ {base = base}) → ∙-π₁ r (∙-π₁ s t) ≡ ∙-π₁ (∙-π₁ r s) t
assocπ₁ r s t = elim3 eqIsSet baseProof r s t where
  eqIsSet : ∀ r' s' t' → isSet (∙-π₁ r' (∙-π₁ s' t') ≡ ∙-π₁ (∙-π₁ r' s') t')
  eqIsSet r' s' t' = ≡π₁IsSet (∙-π₁ r' (∙-π₁ s' t')) (∙-π₁ (∙-π₁ r' s') t')
  baseProof : ∀ (l1 l2 l3 : Ω) → ∙-π₁ ∣ l1 ∣₂ (∙-π₁ ∣ l2 ∣₂ ∣ l3 ∣₂) ≡ ∙-π₁ (∙-π₁ ∣ l1 ∣₂ ∣ l2 ∣₂) ∣ l3 ∣₂
  baseProof l1 l2 l3 =
    ∙-π₁ ∣ l1 ∣₂ (∙-π₁ ∣ l2 ∣₂ ∣ l3 ∣₂)
    ≡⟨ refl ⟩
    ∣ l1 ∙ (l2 ∙ l3) ∣₂
    ≡⟨ cong (λ l → ∣ l ∣₂) (assoc l1 l2 l3) ⟩
    ∣ (l1 ∙ l2) ∙ l3 ∣₂
    ≡⟨ refl ⟩
    ∙-π₁ (∙-π₁ ∣ l1 ∣₂ ∣ l2 ∣₂) ∣ l3 ∣₂ ∎

rUnitπ₁ : ∀ (r : π₁ {base = base}) → r ≡ ∙-π₁ r 1π₁
rUnitπ₁ = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (r' ≡ ∙-π₁ r' 1π₁)
  eqIsSet r' = ≡π₁IsSet r' (∙-π₁ r' 1π₁)
  baseProof : ∀ (l : Ω) → ∣ l ∣₂ ≡ ∙-π₁ ∣ l ∣₂ 1π₁
  baseProof l =
    ∣ l ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (rUnit l) ⟩
    ∣ l ∙ refl ∣₂
    ≡⟨ refl ⟩
    ∙-π₁ ∣ l ∣₂ 1π₁ ∎

lUnitπ₁ : ∀ (r : π₁ {base = base}) → r ≡ ∙-π₁ 1π₁ r
lUnitπ₁ = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (r' ≡ ∙-π₁ 1π₁ r')
  eqIsSet r' = ≡π₁IsSet r' (∙-π₁ 1π₁ r')
  baseProof : ∀ (l : Ω) → ∣ l ∣₂ ≡ ∙-π₁ 1π₁ ∣ l ∣₂
  baseProof l =
    ∣ l ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (lUnit l) ⟩
    ∣ refl ∙ l ∣₂
    ≡⟨ refl ⟩
    ∙-π₁ 1π₁ ∣ l ∣₂ ∎

rCancelπ₁ : ∀ (r : π₁ {base = base}) → ∙-π₁ r (invπ₁ r) ≡ 1π₁
rCancelπ₁ = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (∙-π₁ r' (invπ₁ r') ≡ 1π₁)
  eqIsSet r' = ≡π₁IsSet (∙-π₁ r' (invπ₁ r')) 1π₁
  baseProof : ∀ (l : Ω) → ∙-π₁ ∣ l ∣₂ (invπ₁ ∣ l ∣₂) ≡ 1π₁
  baseProof l =
    ∙-π₁ ∣ l ∣₂ (invπ₁ ∣ l ∣₂)
    ≡⟨ refl ⟩
    ∙-π₁ ∣ l ∣₂ ∣ sym l ∣₂
    ≡⟨ refl ⟩
    ∣ l ∙ (sym l) ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (rCancel l) ⟩
    ∣ refl ∣₂ ∎

lCancelπ₁ : ∀ (r : π₁ {base = base}) → ∙-π₁ (invπ₁ r) r ≡ 1π₁
lCancelπ₁ = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (∙-π₁ (invπ₁ r') r' ≡ 1π₁)
  eqIsSet r' = ≡π₁IsSet (∙-π₁ (invπ₁ r') r') 1π₁
  baseProof : ∀ (l : Ω) → ∙-π₁ (invπ₁ ∣ l ∣₂) ∣ l ∣₂ ≡ 1π₁
  baseProof l =
    ∙-π₁ (invπ₁ ∣ l ∣₂) ∣ l ∣₂
    ≡⟨ refl ⟩
    ∙-π₁ ∣ sym l ∣₂ ∣ l ∣₂
    ≡⟨ refl ⟩
    ∣ (sym l) ∙ l ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (lCancel l) ⟩
    ∣ refl ∣₂ ∎

π₁IsSemiGroup : IsSemigroup {A = π₁ {base = base}} ∙-π₁
π₁IsSemiGroup = issemigroup π₁IsSet assocπ₁

π₁IsMonoid : IsMonoid {A = π₁ {base = base}} 1π₁ ∙-π₁
π₁IsMonoid = ismonoid π₁IsSemiGroup (λ x → sym (rUnitπ₁ x) , sym (lUnitπ₁ x))

π₁IsGroup : IsGroup {G = π₁ {base = base}} 1π₁ ∙-π₁ invπ₁
π₁IsGroup = isgroup π₁IsMonoid (λ x → rCancelπ₁ x , lCancelπ₁ x)

π₁GroupStr : GroupStr (π₁ {base = base})
π₁GroupStr = groupstr 1π₁ ∙-π₁ invπ₁ π₁IsGroup

π₁Group : ∀ {ℓ}{A : Type ℓ}{base : A} → Group ℓ
π₁Group {base = base} = π₁ {base = base} , π₁GroupStr
