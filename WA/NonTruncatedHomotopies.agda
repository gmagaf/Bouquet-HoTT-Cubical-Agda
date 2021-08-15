{-

This file contains:

- Definition of encode decode functions
- Proof that for all x : W A → p : base ≡ x → decode x (encode x p) ≡ p (no truncations)
- Proof of the truncated versions of encodeDecode and of right-homotopy

-}
{-# OPTIONS --cubical #-}

module WA.WA.NonTruncatedHomotopies where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.HITs.PropositionalTruncation renaming (rec to propRec)
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.SetTruncation hiding (rec2)

open import WA.WA.Base
open import WA.WA.CodeWindingLooping
open import WA.FreeGroupoid
open import WA.FundamentalGroup

-- Definition of the encode - decode functions over the family of types Π(x : W A) → code x

encode : ∀ {ℓ}{A : Type ℓ} → (x : W A) → base ≡ x → code x
encode x l = subst code l e

substPathsR : ∀{ℓ}{C : Type ℓ}{y z : C} → (x : C) → (p : y ≡ z) → subst (λ y → x ≡ y) p ≡ λ q → q ∙ p
substPathsR {ℓ = ℓ} {y = y} x p = funExt homotopy where
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

substFunctions : ∀{ℓ ℓ'}{A : Type ℓ}{B C : A → Type ℓ'}{x y : A}
        → (p : x ≡ y)
        → (f : B x → C x)
        → subst (λ z → (B z → C z)) p f ≡ subst C p ∘ f ∘ subst B (sym p)
substFunctions {ℓ' = ℓ'} {B = B} {C = C} {x = x} p f =  J P d p where
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

decode : ∀ {ℓ}{A : Type ℓ} → (x : W A) → code x → base ≡ x
decode {A = A} base       = looping
decode {A = A} (loop a i) = path i where
  pathover : PathP (λ i → (code (loop a i) → base ≡ (loop a i))) looping (subst (λ z → (code z → base ≡ z)) (loop a) looping)
  pathover = subst-filler (λ z → (code z → base ≡ z)) (loop a) looping
  aux : (a : A) → subst code (sym (loop a)) ≡ automorhpism (inv (η a))
  aux a = funExt homotopy where
    homotopy : ∀ (g : FreeGroupoid A) → subst code (sym (loop a)) g ≡ automorhpism (inv (η a)) g
    homotopy g =
      subst code (sym (loop a)) g
      ≡⟨ refl ⟩
      transport (sym (pathsInU (η a))) g
      ≡⟨ cong (λ x → transport x g) (sym (invPathsInUNaturality (η a))) ⟩
      transport (pathsInU (inv (η a))) g
      ≡⟨ uaβ  (equivs (inv (η a))) g ⟩
      automorhpism (inv (η a)) g ∎
  calculations : ∀ (a : A) → ∀ g → looping (m g (inv (η a))) ∙ loop a ≡ looping g
  calculations a g =
    looping (m g (inv (η a))) ∙ loop a
    ≡⟨ refl ⟩
    (looping g ∙ (sym (loop a))) ∙ loop a
    ≡⟨ sym (pathAssoc (looping g) (sym (loop a)) (loop a)) ⟩
    looping g ∙ (sym (loop a) ∙ loop a)
    ≡⟨ cong (λ x → looping g ∙ x) (lCancel (loop a)) ⟩
    looping g ∙ refl
    ≡⟨ sym (rUnit (looping g)) ⟩
    looping g ∎
  path' : subst (λ z → (code z → base ≡ z)) (loop a) looping ≡ looping
  path' =
    subst (λ z → (code z → base ≡ z)) (loop a) looping
    ≡⟨ substFunctions {B = code} {C = λ z → base ≡ z} (loop a) looping ⟩
    subst (λ z → base ≡ z) (loop a) ∘ looping ∘ subst code (sym (loop a))
    ≡⟨ cong (λ x → x ∘ looping ∘ subst code (sym (loop a))) (substPathsR base (loop a)) ⟩
    (λ p → p ∙ loop a) ∘ looping ∘ subst code (sym (loop a))
    ≡⟨ cong (λ x → (λ p → p ∙ loop a) ∘ looping ∘ x) (aux a) ⟩
    (λ p → p ∙ loop a) ∘ looping ∘ automorhpism (inv (η a))
    ≡⟨ refl ⟩
    (λ p → p ∙ loop a) ∘ looping ∘ (λ g → m g (inv (η a)))
    ≡⟨ refl ⟩
    (λ p → p ∙ loop a) ∘ (λ g → looping (m g (inv (η a))))
    ≡⟨ refl ⟩
    (λ g → looping (m g (inv (η a))) ∙ loop a)
    ≡⟨ funExt (calculations a) ⟩
    (λ g → looping g)
    ≡⟨ refl ⟩
    looping ∎
  path'' : PathP (λ i → code ((loop a ∙ refl) i) → base ≡ ((loop a ∙ refl) i)) looping looping
  path'' = compPathP' {A = W A} {B = λ z → code z → base ≡ z} pathover path'
  p''≡p : PathP (λ i → code ((loop a ∙ refl) i) → base ≡ ((loop a ∙ refl) i)) looping looping ≡
          PathP (λ i → code (loop a i) → base ≡ (loop a i)) looping looping
  p''≡p = cong (λ x → PathP (λ i → code (x i) → base ≡ (x i)) looping looping) (sym (rUnit (loop a)))
  path : PathP (λ i → code (loop a i) → base ≡ (loop a i)) looping looping
  path = transport p''≡p path''

-- Non truncated Left Homotopy

decodeEncode : ∀ {ℓ}{A : Type ℓ} → (x : W A) → (p : base ≡ x) → decode x (encode x p) ≡ p
decodeEncode {ℓ = ℓ} {A = A} x p = J P d p where
  P : ∀ x' → base ≡ x' → Type ℓ
  P x' p' = decode x' (encode x' p') ≡ p'
  d : P base refl
  d =
    decode base (encode {A = A} base refl)
    ≡⟨ refl ⟩
    looping (subst (code {A = A}) (refl {x = base}) e)
    ≡⟨ refl ⟩
    looping (transport (cong (code {A = A}) (refl {x = base})) (e {A = A}))
    ≡⟨ cong (λ e' → looping e') (transportRefl (e {A = A})) ⟩
    looping e
    ≡⟨ refl ⟩
    refl ∎

left-homotopy : ∀ {ℓ}{A : Type ℓ} → ∀ (l : ΩWA {A = A}) → looping (winding l) ≡ l
left-homotopy l = decodeEncode base l

-- Truncated proofs of right homotopy of winding/looping functions

truncatedPathEquality : ∀ {ℓ}{A : Type ℓ} → (g : FreeGroupoid A) → ∥ cong code (looping g) ≡ ua (equivs g) ∥
truncatedPathEquality = elimProp
            Bprop
            (λ a → ∣ η-ind a ∣)
            (λ g1 g2 → λ ∣ind1∣ ∣ind2∣ → rec2 squash (λ ind1 ind2 → ∣ m-ind g1 g2 ind1 ind2 ∣) ∣ind1∣ ∣ind2∣)
            ∣ e-ind ∣
            (λ g → λ ∣ind∣ → propRec squash (λ ind → ∣ inv-ind g ind ∣) ∣ind∣) where
  B : ∀ g → Type _
  B g = cong code (looping g) ≡ ua (equivs g)
  Bprop : ∀ g → isProp ∥ B g ∥
  Bprop g = squash
  η-ind : ∀ a → B (η a)
  η-ind a = refl
  m-ind : ∀ g1 g2 → B g1 → B g2 → B (m g1 g2)
  m-ind g1 g2 ind1 ind2 =
    cong code (looping (m g1 g2))
    ≡⟨ refl ⟩
    cong code (looping g1) ∙ cong code (looping g2)
    ≡⟨ cong (λ x → x ∙ cong code (looping g2)) ind1 ⟩
    pathsInU g1 ∙ cong code (looping g2)
    ≡⟨ cong (λ x → pathsInU g1 ∙ x) ind2 ⟩
    pathsInU g1 ∙ pathsInU g2
    ≡⟨ sym (multPathsInUNaturality g1 g2) ⟩
    pathsInU (m g1 g2) ∎
  e-ind : B e
  e-ind =
    cong code (looping e)
    ≡⟨ refl ⟩
    refl
    ≡⟨ sym idPathsInUNaturality ⟩
    pathsInU e ∎
  inv-ind : ∀ g → B g → B (inv g)
  inv-ind g ind =
    cong code (looping (inv g))
    ≡⟨ refl ⟩
    sym (cong code (looping g))
    ≡⟨ cong sym ind ⟩
    sym (pathsInU g)
    ≡⟨ sym (invPathsInUNaturality g) ⟩
    ua (equivs (inv g)) ∎

truncatedRight-homotopy : ∀ {ℓ}{A : Type ℓ} → (g : FreeGroupoid A) → ∥ winding (looping g) ≡ g ∥
truncatedRight-homotopy g = propRec squash recursion (truncatedPathEquality g) where
  recursion : cong code (looping g) ≡ ua (equivs g) → ∥ winding (looping g) ≡ g ∥
  recursion hyp = ∣ aux ∣ where
    aux : winding (looping g) ≡ g
    aux =
      winding (looping g)
      ≡⟨ refl ⟩
      subst code (looping g) e
      ≡⟨ refl ⟩
      transport (cong code (looping g)) e
      ≡⟨ cong (λ x → transport x e) hyp ⟩
      transport (ua (equivs g)) e
      ≡⟨ uaβ  (equivs g) e ⟩
      m e g
      ≡⟨ sym (idl g) ⟩
      g ∎

right-homotopyInTruncatedGroupoid : ∀ {ℓ}{A : Type ℓ} → (g : FreeGroupoid A) → ∣ winding (looping g) ∣₂ ≡ ∣ g ∣₂
right-homotopyInTruncatedGroupoid g = Iso.inv PathIdTrunc₀Iso (truncatedRight-homotopy g)

-- Truncated encodeDecode over all fibrations

truncatedEncodeDecode : ∀ {ℓ}{A : Type ℓ} → (x : W A) → (g : code x) → ∥ encode x (decode x g) ≡ g ∥
truncatedEncodeDecode base = truncatedRight-homotopy
truncatedEncodeDecode {A = A} (loop a i) = isProp→PathP prop truncatedRight-homotopy truncatedRight-homotopy i where
  prop : ∀ i → isProp (∀ (g : code (loop a i)) → ∥ encode (loop a i) (decode (loop a i) g) ≡ g ∥)
  prop i f g = funExt pointwise where
    pointwise : (x : code (loop a i)) → PathP (λ _ → ∥ encode (loop a i) (decode (loop a i) x) ≡ x ∥) (f x) (g x)
    pointwise x = isProp→PathP (λ i → squash) (f x) (g x)

encodeDecodeInTruncatedGroupoid : ∀ {ℓ}{A : Type ℓ} → (x : W A) → (g : code x) → ∣ encode x (decode x g) ∣₂ ≡ ∣ g ∣₂
encodeDecodeInTruncatedGroupoid x g = Iso.inv PathIdTrunc₀Iso (truncatedEncodeDecode x g)
