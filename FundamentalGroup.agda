{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

open import Cubical.HITs.SetTruncation
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base

module WA.FundamentalGroup {ℓ} {A : Type ℓ} {base : A} where


Ω : Type ℓ
Ω = base ≡ base

π₁ : Type ℓ
π₁ = ∥ Ω ∥₂


-- Some Properties of the fundamental group

π₁IsSet : isSet π₁
π₁IsSet = squash₂

≡πIsProp : ∀ (r s : π₁) → isProp (r ≡ s)
≡πIsProp r s = squash₂ r s

≡πIsSet : ∀ (r s : π₁) → isSet (r ≡ s)
≡πIsSet r s = isProp→isSet (≡πIsProp r s)

1π₁ : π₁
1π₁ = ∣ refl ∣₂

invπ₁ : π₁ → π₁
invπ₁ r = rec π₁IsSet symLoopClass r where
  symLoopClass : Ω → π₁
  symLoopClass p = ∣ sym p ∣₂

∙-π₁ : π₁ → π₁ → π₁
∙-π₁ r s = rec π₁IsSet sndRec s where
  sndRec : Ω → π₁
  sndRec q = rec π₁IsSet (λ p → ∣ p ∙ q ∣₂) r

assocπ₁ : ∀ r s t → ∙-π₁ r (∙-π₁ s t) ≡ ∙-π₁ (∙-π₁ r s) t
assocπ₁ r s t = elim eqIsSet1 baseProof1 r where
  eqIsSet1 : ∀ r' → isSet (∙-π₁ r' (∙-π₁ s t) ≡ ∙-π₁ (∙-π₁ r' s) t)
  eqIsSet1 r' = ≡πIsSet (∙-π₁ r' (∙-π₁ s t)) (∙-π₁ (∙-π₁ r' s) t)
  baseProof1 : ∀ l1 → ∙-π₁ ∣ l1 ∣₂ (∙-π₁ s t) ≡ ∙-π₁ (∙-π₁ ∣ l1 ∣₂ s) t
  baseProof1 l1 = elim eqIsSet2 baseProof2 s where
    eqIsSet2 : ∀ s' → isSet (∙-π₁ ∣ l1 ∣₂ (∙-π₁ s' t) ≡ ∙-π₁ (∙-π₁ ∣ l1 ∣₂ s') t)
    eqIsSet2 s' = ≡πIsSet (∙-π₁ ∣ l1 ∣₂ (∙-π₁ s' t)) (∙-π₁ (∙-π₁ ∣ l1 ∣₂ s') t)
    baseProof2 : ∀ l2 → ∙-π₁ ∣ l1 ∣₂ (∙-π₁ ∣ l2 ∣₂ t) ≡ ∙-π₁ (∙-π₁ ∣ l1 ∣₂ ∣ l2 ∣₂) t
    baseProof2 l2 = elim eqIsSet3 baseProof3 t where
      eqIsSet3 : ∀ t' → isSet (∙-π₁ ∣ l1 ∣₂ (∙-π₁ ∣ l2 ∣₂ t') ≡ ∙-π₁ (∙-π₁ ∣ l1 ∣₂ ∣ l2 ∣₂) t')
      eqIsSet3 t' = ≡πIsSet (∙-π₁ ∣ l1 ∣₂ (∙-π₁ ∣ l2 ∣₂ t')) (∙-π₁ (∙-π₁ ∣ l1 ∣₂ ∣ l2 ∣₂) t')
      baseProof3 : ∀ (l3 : Ω) → ∙-π₁ ∣ l1 ∣₂ (∙-π₁ ∣ l2 ∣₂ ∣ l3 ∣₂) ≡ ∙-π₁ (∙-π₁ ∣ l1 ∣₂ ∣ l2 ∣₂) ∣ l3 ∣₂
      baseProof3 l3 =
        ∙-π₁ ∣ l1 ∣₂ (∙-π₁ ∣ l2 ∣₂ ∣ l3 ∣₂)
        ≡⟨ refl ⟩
        ∣ l1 ∙ (l2 ∙ l3) ∣₂
        ≡⟨ cong (λ l → ∣ l ∣₂) (assoc l1 l2 l3) ⟩
        ∣ (l1 ∙ l2) ∙ l3 ∣₂
        ≡⟨ refl ⟩
        ∙-π₁ (∙-π₁ ∣ l1 ∣₂ ∣ l2 ∣₂) ∣ l3 ∣₂ ∎

rUnitπ₁ : ∀ r → r ≡ ∙-π₁ r 1π₁
rUnitπ₁ = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (r' ≡ ∙-π₁ r' 1π₁)
  eqIsSet r' = ≡πIsSet r' (∙-π₁ r' 1π₁)
  baseProof : ∀ (l : Ω) → ∣ l ∣₂ ≡ ∙-π₁ ∣ l ∣₂ 1π₁
  baseProof l =
    ∣ l ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (rUnit l) ⟩
    ∣ l ∙ refl ∣₂
    ≡⟨ refl ⟩
    ∙-π₁ ∣ l ∣₂ 1π₁ ∎

lUnitπ₁ : ∀ r → r ≡ ∙-π₁ 1π₁ r
lUnitπ₁ = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (r' ≡ ∙-π₁ 1π₁ r')
  eqIsSet r' = ≡πIsSet r' (∙-π₁ 1π₁ r')
  baseProof : ∀ (l : Ω) → ∣ l ∣₂ ≡ ∙-π₁ 1π₁ ∣ l ∣₂
  baseProof l =
    ∣ l ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (lUnit l) ⟩
    ∣ refl ∙ l ∣₂
    ≡⟨ refl ⟩
    ∙-π₁ 1π₁ ∣ l ∣₂ ∎

rCancelπ₁ : ∀ r → ∙-π₁ r (invπ₁ r) ≡ 1π₁
rCancelπ₁ = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (∙-π₁ r' (invπ₁ r') ≡ 1π₁)
  eqIsSet r' = ≡πIsSet (∙-π₁ r' (invπ₁ r')) 1π₁
  baseProof : ∀ (l : Ω) → ∙-π₁ ∣ l ∣₂ (invπ₁ ∣ l ∣₂) ≡ 1π₁
  baseProof l =
    ∙-π₁ ∣ l ∣₂ (invπ₁ ∣ l ∣₂)
    ≡⟨ refl ⟩
    ∙-π₁ ∣ l ∣₂ ∣ sym l ∣₂
    ≡⟨ refl ⟩
    ∣ l ∙ (sym l) ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (rCancel l) ⟩
    ∣ refl ∣₂ ∎

lCancelπ₁ : ∀ r → ∙-π₁ (invπ₁ r) r ≡ 1π₁
lCancelπ₁ = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (∙-π₁ (invπ₁ r') r' ≡ 1π₁)
  eqIsSet r' = ≡πIsSet (∙-π₁ (invπ₁ r') r') 1π₁
  baseProof : ∀ (l : Ω) → ∙-π₁ (invπ₁ ∣ l ∣₂) ∣ l ∣₂ ≡ 1π₁
  baseProof l =
    ∙-π₁ (invπ₁ ∣ l ∣₂) ∣ l ∣₂
    ≡⟨ refl ⟩
    ∙-π₁ ∣ sym l ∣₂ ∣ l ∣₂
    ≡⟨ refl ⟩
    ∣ (sym l) ∙ l ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (lCancel l) ⟩
    ∣ refl ∣₂ ∎

π₁IsSemiGroup : IsSemigroup ∙-π₁
π₁IsSemiGroup = issemigroup π₁IsSet assocπ₁

π₁IsMonoid : IsMonoid 1π₁ ∙-π₁
π₁IsMonoid = ismonoid π₁IsSemiGroup (λ x → sym (rUnitπ₁ x) , sym (lUnitπ₁ x))

π₁IsGroup : IsGroup 1π₁ ∙-π₁ invπ₁
π₁IsGroup = isgroup π₁IsMonoid (λ x → rCancelπ₁ x , lCancelπ₁ x)

π₁GroupStr : GroupStr π₁
π₁GroupStr = groupstr 1π₁ ∙-π₁ invπ₁ π₁IsGroup

π₁Group : Group ℓ
π₁Group = π₁ , π₁GroupStr
