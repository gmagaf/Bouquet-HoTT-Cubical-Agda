{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetTruncation
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import WA.WA
open import WA.FundamentalGroup

module WA.LeftHomotopy where

data FreeGroupoid {ℓ}(A : Type ℓ) : Type ℓ where
  η : A → FreeGroupoid A
  m : FreeGroupoid A → FreeGroupoid A → FreeGroupoid A
  e : FreeGroupoid A
  inv : FreeGroupoid A → FreeGroupoid A
  assoc : ∀ x y z → m x (m y z) ≡ m (m x y) z
  idr : ∀ x → x ≡ m x e
  idl : ∀ x → x ≡  m e x
  invr : ∀ x → m x (inv x) ≡ e
  invl : ∀ x → m (inv x) x ≡ e

ΩWA : ∀ {ℓ}{A : Type ℓ} → Type ℓ
ΩWA {A = A} = Ω {A = W A} {base = base}

loopingoid : ∀ {ℓ}{A : Type ℓ} → FreeGroupoid A → ΩWA
loopingoid (η a) = loop a
loopingoid (m g1 g2) = loopingoid g1 ∙ loopingoid g2
loopingoid e = refl
loopingoid (inv g) = sym (loopingoid g)
loopingoid (assoc g1 g2 g3 i) = pathAssoc (loopingoid g1) (loopingoid g2) (loopingoid g3) i
loopingoid (idr g i) = rUnit (loopingoid g) i
loopingoid (idl g i) = lUnit (loopingoid g) i
loopingoid (invr g i) = rCancel (loopingoid g) i
loopingoid (invl g i) = lCancel (loopingoid g) i

automorhpism : ∀ {ℓ}{A : Type ℓ} → FreeGroupoid A → FreeGroupoid A → FreeGroupoid A
automorhpism a g = m g a

invAutomorhpism : ∀ {ℓ}{A : Type ℓ} → FreeGroupoid A → FreeGroupoid A → FreeGroupoid A
invAutomorhpism a = automorhpism (inv a)
rhomotopy : ∀ {ℓ}{A : Type ℓ} → ∀ (a : FreeGroupoid A) → ∀ (g : FreeGroupoid A) → (automorhpism a) (invAutomorhpism a g) ≡ g
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
lhomotopy : ∀ {ℓ}{A : Type ℓ} → ∀ (a : FreeGroupoid A) → ∀ (g : FreeGroupoid A) → invAutomorhpism a ((automorhpism a) g) ≡ g
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

biInvAutomorphisms : ∀ {ℓ}{A : Type ℓ} → FreeGroupoid A → BiInvEquiv (FreeGroupoid A) (FreeGroupoid A)
biInvAutomorphisms a = biInvEquiv (automorhpism a) (invAutomorhpism a) (rhomotopy a) (invAutomorhpism a) (lhomotopy a)

equivs : ∀ {ℓ}{A : Type ℓ} → FreeGroupoid A → (FreeGroupoid A) ≃ (FreeGroupoid A)
equivs a = biInvEquiv→Equiv-right (biInvAutomorphisms a)

pathsInU : ∀ {ℓ}{A : Type ℓ} →  FreeGroupoid A → (FreeGroupoid A) ≡ (FreeGroupoid A)
pathsInU a = ua (equivs a)

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

code : ∀ {ℓ}{A : Type ℓ} → (W A) → Type ℓ
code {A = A} base = (FreeGroupoid A)
code (loop a i)   = pathsInU (η a) i

aux3 : ∀ {ℓ}{A : Type ℓ}(a : A) → subst code (sym (loop a)) ≡ automorhpism (inv (η a))
aux3 {A = A} a = funExt homotopy where
  homotopy : ∀ (g : FreeGroupoid A) → subst code (sym (loop a)) g ≡ automorhpism (inv (η a)) g
  homotopy g =
    subst code (sym (loop a)) g
    ≡⟨ refl ⟩
    transport (cong code (sym (loop a))) g
    ≡⟨ refl ⟩
    transport (sym (cong code (loop a))) g
    ≡⟨ refl ⟩
    transport (sym (ua (equivs (η a)))) g
    ≡⟨ cong (λ f → f g) (sym (transportUaInv (equivs (η a)))) ⟩
    transport (ua (invEquiv (equivs (η a)))) g
    ≡⟨ cong (λ x → transport (ua x) g) (naturalityOfInvEquivs (η a)) ⟩
    transport (ua (equivs (inv (η a)))) g
    ≡⟨ uaβ  (equivs (inv (η a))) g ⟩
    automorhpism (inv (η a)) g ∎

aux2 : ∀{ℓ}{C : Type ℓ}{y z : C} → (x : C) → (p : y ≡ z) → subst (λ y → x ≡ y) p ≡ λ q → q ∙ p
aux2 {ℓ = ℓ} {y = y} x p = funExt homotopy where
  homotopy : ∀ q → subst (λ y → x ≡ y) p q ≡ q ∙ p
  homotopy q = J P d p where
    P : ∀ z' → y ≡ z' → Type ℓ
    P z' p' = subst (λ y → x ≡ y) p' q ≡ q ∙ p'
    d : P y refl
    d =
      subst (λ y → x ≡ y) refl q
      ≡⟨ substRefl {B = λ y → x ≡ y} q ⟩
      q
      ≡⟨ rUnit q ⟩
      q ∙ refl ∎

aux1 : ∀{ℓ ℓ'}{A : Type ℓ}{B C : A → Type ℓ'}{x y : A}
                → (p : x ≡ y)
                → (f : B x → C x)
                → subst (λ z → (B z → C z)) p f ≡ subst C p ∘ f ∘ subst B (sym p)
aux1 {ℓ' = ℓ'} {B = B} {C = C} {x = x} p f =  J P d p where
  auxC : idfun (C x) ≡ subst C refl
  auxC = funExt (λ c → sym (substRefl {B = C} c))
  auxB : idfun (B x) ≡ subst B refl
  auxB = funExt (λ b → sym (substRefl {B = B} b))
  P : ∀ y' → x ≡ y' → Type ℓ'
  P y' p' = subst (λ z → (B z → C z)) p' f ≡ subst C p' ∘ f ∘ subst B (sym p')
  d : P x refl
  d =
    subst (λ z → (B z → C z)) refl f
    ≡⟨ substRefl {B = λ z → (B z → C z)} f ⟩
    f
    ≡⟨ refl ⟩
    idfun (C x) ∘ f ∘ idfun (B x)
    ≡⟨ cong (λ h → h ∘ f ∘ idfun (B x)) auxC ⟩
    subst C refl ∘ f ∘ idfun (B x)
    ≡⟨ cong (λ h → subst C refl ∘ f ∘ h) auxB ⟩
    subst C refl ∘ f ∘ subst B refl
    ≡⟨ refl ⟩
    subst C refl ∘ f ∘ subst B (sym refl) ∎

encode : ∀ {ℓ}{A : Type ℓ} → (x : W A) → base ≡ x → code x
encode x l = subst code l e

decode : ∀ {ℓ}{A : Type ℓ} → (x : W A) → code x → base ≡ x
decode {A = A} base       = loopingoid
decode {A = A} (loop a i) = path i where
  pathover : PathP (λ i → (code (loop a i) → base ≡ (loop a i))) loopingoid (subst (λ z → (code z → base ≡ z)) (loop a) loopingoid)
  pathover = subst-filler (λ z → (code z → base ≡ z)) (loop a) loopingoid
  calculations : ∀ (a : A) → ∀ g → loopingoid (m g (inv (η a))) ∙ loop a ≡ loopingoid g
  calculations a g =
    loopingoid (m g (inv (η a))) ∙ loop a
    ≡⟨ refl ⟩
    (loopingoid g ∙ (sym (loop a))) ∙ loop a
    ≡⟨ sym (pathAssoc (loopingoid g) (sym (loop a)) (loop a)) ⟩
    loopingoid g ∙ (sym (loop a) ∙ loop a)
    ≡⟨ cong (λ x → loopingoid g ∙ x) (lCancel (loop a)) ⟩
    loopingoid g ∙ refl
    ≡⟨ sym (rUnit (loopingoid g)) ⟩
    loopingoid g ∎
  path' : subst (λ z → (code z → base ≡ z)) (loop a) loopingoid ≡ loopingoid
  path' =
    subst (λ z → (code z → base ≡ z)) (loop a) loopingoid
    ≡⟨ aux1 {B = code} {C = λ z → base ≡ z} (loop a) loopingoid ⟩
    subst (λ z → base ≡ z) (loop a) ∘ loopingoid ∘ subst code (sym (loop a))
    ≡⟨ cong (λ x → x ∘ loopingoid ∘ subst code (sym (loop a))) (aux2 base (loop a)) ⟩
    (λ p → p ∙ loop a) ∘ loopingoid ∘ subst code (sym (loop a))
    ≡⟨ cong (λ x → (λ p → p ∙ loop a) ∘ loopingoid ∘ x) (aux3 a) ⟩
    (λ p → p ∙ loop a) ∘ loopingoid ∘ automorhpism (inv (η a))
    ≡⟨ refl ⟩
    (λ p → p ∙ loop a) ∘ loopingoid ∘ (λ g → m g (inv (η a)))
    ≡⟨ refl ⟩
    (λ p → p ∙ loop a) ∘ (λ g → loopingoid (m g (inv (η a))))
    ≡⟨ refl ⟩
    (λ g → loopingoid (m g (inv (η a))) ∙ loop a)
    ≡⟨ funExt (calculations a) ⟩
    (λ g → loopingoid g)
    ≡⟨ refl ⟩
    loopingoid ∎
  path'' : PathP (λ i → code ((loop a ∙ refl) i) → base ≡ ((loop a ∙ refl) i)) loopingoid loopingoid
  path'' = compPathP' {A = W A} {B = λ z → code z → base ≡ z} pathover path'
  p''≡p : PathP (λ i → code ((loop a ∙ refl) i) → base ≡ ((loop a ∙ refl) i)) loopingoid loopingoid ≡
          PathP (λ i → code (loop a i) → base ≡ (loop a i)) loopingoid loopingoid
  p''≡p = cong (λ x → PathP (λ i → code (x i) → base ≡ (x i)) loopingoid loopingoid) (sym (rUnit (loop a)))
  path : PathP (λ i → code (loop a i) → base ≡ (loop a i)) loopingoid loopingoid
  path = transport p''≡p path''

decodeEncode : ∀ {ℓ}{A : Type ℓ} → (x : W A) → (p : base ≡ x) → decode x (encode x p) ≡ p
decodeEncode {ℓ = ℓ} {A = A} x p = J P d p where
  P : ∀ x' → base ≡ x' → Type ℓ
  P x' p' = decode x' (encode x' p') ≡ p'
  d : P base refl
  d =
    decode base (encode {A = A} base refl)
    ≡⟨ refl ⟩
    loopingoid (subst (code {A = A}) (refl {x = base}) e)
    ≡⟨ refl ⟩
    loopingoid (transport (cong (code {A = A}) (refl {x = base})) (e {A = A}))
    ≡⟨ cong (λ e' → loopingoid e') (transportRefl (e {A = A})) ⟩
    loopingoid e
    ≡⟨ refl ⟩
    refl ∎

-- left-homotopy : ∀ {ℓ}{A : Type ℓ} → ∀ (r : π₁WA {A = A}) → looping (winding r) ≡ r
-- left-homotopy r = elim Bset ind r where
--   Bset : ∀ r' → isSet (looping (winding r') ≡ r')
--   Bset r' = isProp→isSet (≡πIsProp (looping (winding r')) r')
--   ind : ∀ (l : ΩWA) → looping (winding ∣ l ∣₂) ≡ ∣ l ∣₂
--   ind l =
--     looping (winding ∣ l ∣₂)
--     ≡⟨ refl ⟩
--     looping (subst code l e)
--     ≡⟨ {!  !} ⟩
--     ∣ l ∣₂ ∎
