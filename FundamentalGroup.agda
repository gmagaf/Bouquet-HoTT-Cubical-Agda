{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

open import Cubical.HITs.SetTruncation.Base
open import Cubical.HITs.SetTruncation.Properties
open import Cubical.Foundations.GroupoidLaws

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

idLoop : π₁
idLoop = ∣ refl ∣₂

invLoop : π₁ → π₁
invLoop r = rec π₁IsSet symLoopClass r where
  symLoopClass : Ω → π₁
  symLoopClass p = ∣ sym p ∣₂

concLoops : π₁ → π₁ → π₁
concLoops r s = rec π₁IsSet sndRec s where
  sndRec : Ω → π₁
  sndRec q = rec π₁IsSet (λ p → ∣ p ∙ q ∣₂) r

assocLoops : ∀ r s t → concLoops r (concLoops s t) ≡ concLoops (concLoops r s) t
assocLoops r s t = elim eqIsSet1 baseProof1 r where
  eqIsSet1 : ∀ r' → isSet (concLoops r' (concLoops s t) ≡ concLoops (concLoops r' s) t)
  eqIsSet1 r' = ≡πIsSet (concLoops r' (concLoops s t)) (concLoops (concLoops r' s) t)
  baseProof1 : ∀ l1 → concLoops ∣ l1 ∣₂ (concLoops s t) ≡ concLoops (concLoops ∣ l1 ∣₂ s) t
  baseProof1 l1 = elim eqIsSet2 baseProof2 s where
    eqIsSet2 : ∀ s' → isSet (concLoops ∣ l1 ∣₂ (concLoops s' t) ≡ concLoops (concLoops ∣ l1 ∣₂ s') t)
    eqIsSet2 s' = ≡πIsSet (concLoops ∣ l1 ∣₂ (concLoops s' t)) (concLoops (concLoops ∣ l1 ∣₂ s') t)
    baseProof2 : ∀ l2 → concLoops ∣ l1 ∣₂ (concLoops ∣ l2 ∣₂ t) ≡ concLoops (concLoops ∣ l1 ∣₂ ∣ l2 ∣₂) t
    baseProof2 l2 = elim eqIsSet3 baseProof3 t where
      eqIsSet3 : ∀ t' → isSet (concLoops ∣ l1 ∣₂ (concLoops ∣ l2 ∣₂ t') ≡ concLoops (concLoops ∣ l1 ∣₂ ∣ l2 ∣₂) t')
      eqIsSet3 t' = ≡πIsSet (concLoops ∣ l1 ∣₂ (concLoops ∣ l2 ∣₂ t')) (concLoops (concLoops ∣ l1 ∣₂ ∣ l2 ∣₂) t')
      baseProof3 : ∀ (l3 : Ω) → concLoops ∣ l1 ∣₂ (concLoops ∣ l2 ∣₂ ∣ l3 ∣₂) ≡ concLoops (concLoops ∣ l1 ∣₂ ∣ l2 ∣₂) ∣ l3 ∣₂
      baseProof3 l3 =
        concLoops ∣ l1 ∣₂ (concLoops ∣ l2 ∣₂ ∣ l3 ∣₂)
        ≡⟨ refl ⟩
        ∣ l1 ∙ (l2 ∙ l3) ∣₂
        ≡⟨ cong (λ l → ∣ l ∣₂) (assoc l1 l2 l3) ⟩
        ∣ (l1 ∙ l2) ∙ l3 ∣₂
        ≡⟨ refl ⟩
        concLoops (concLoops ∣ l1 ∣₂ ∣ l2 ∣₂) ∣ l3 ∣₂ ∎

rUnitLoop : ∀ r → r ≡ concLoops r idLoop
rUnitLoop = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (r' ≡ concLoops r' idLoop)
  eqIsSet r' = ≡πIsSet r' (concLoops r' idLoop)
  baseProof : ∀ (l : Ω) → ∣ l ∣₂ ≡ concLoops ∣ l ∣₂ idLoop
  baseProof l =
    ∣ l ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (rUnit l) ⟩
    ∣ l ∙ refl ∣₂
    ≡⟨ refl ⟩
    concLoops ∣ l ∣₂ idLoop ∎

lUnitLoop : ∀ r → r ≡ concLoops idLoop r
lUnitLoop = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (r' ≡ concLoops idLoop r')
  eqIsSet r' = ≡πIsSet r' (concLoops idLoop r')
  baseProof : ∀ (l : Ω) → ∣ l ∣₂ ≡ concLoops idLoop ∣ l ∣₂
  baseProof l =
    ∣ l ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (lUnit l) ⟩
    ∣ refl ∙ l ∣₂
    ≡⟨ refl ⟩
    concLoops idLoop ∣ l ∣₂ ∎

rCancelLoop : ∀ r → concLoops r (invLoop r) ≡ idLoop
rCancelLoop = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (concLoops r' (invLoop r') ≡ idLoop)
  eqIsSet r' = ≡πIsSet (concLoops r' (invLoop r')) idLoop
  baseProof : ∀ (l : Ω) → concLoops ∣ l ∣₂ (invLoop ∣ l ∣₂) ≡ idLoop
  baseProof l =
    concLoops ∣ l ∣₂ (invLoop ∣ l ∣₂)
    ≡⟨ refl ⟩
    concLoops ∣ l ∣₂ ∣ sym l ∣₂
    ≡⟨ refl ⟩
    ∣ l ∙ (sym l) ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (rCancel l) ⟩
    ∣ refl ∣₂ ∎

lCancelLoop : ∀ r → concLoops (invLoop r) r ≡ idLoop
lCancelLoop = elim eqIsSet baseProof where
  eqIsSet : ∀ r' → isSet (concLoops (invLoop r') r' ≡ idLoop)
  eqIsSet r' = ≡πIsSet (concLoops (invLoop r') r') idLoop
  baseProof : ∀ (l : Ω) → concLoops (invLoop ∣ l ∣₂) ∣ l ∣₂ ≡ idLoop
  baseProof l =
    concLoops (invLoop ∣ l ∣₂) ∣ l ∣₂
    ≡⟨ refl ⟩
    concLoops ∣ sym l ∣₂ ∣ l ∣₂
    ≡⟨ refl ⟩
    ∣ (sym l) ∙ l ∣₂
    ≡⟨ cong (λ l' → ∣ l' ∣₂) (lCancel l) ⟩
    ∣ refl ∣₂ ∎
