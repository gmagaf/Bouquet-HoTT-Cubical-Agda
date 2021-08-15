{-

This file contains:

- Properties of the FreeGroup

-}
{-# OPTIONS --cubical #-}

module WA.FreeGroup.Properties where

open import WA.FreeGroup.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible

open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base

private
  variable
    ℓ : Level
    A : Type ℓ

freeGroupIsSet : isSet (FreeGroup A)
freeGroupIsSet = trunc

freeGroupIsSemiGroup : IsSemigroup {A = FreeGroup A} m
freeGroupIsSemiGroup = issemigroup freeGroupIsSet assoc

freeGroupIsMonoid : IsMonoid {A = FreeGroup A} e m
freeGroupIsMonoid = ismonoid freeGroupIsSemiGroup (λ x → sym (idr x) , sym (idl x))

freeGroupIsGroup : IsGroup {G = FreeGroup A} e m inv
freeGroupIsGroup = isgroup freeGroupIsMonoid (λ x → invr x , invl x)

freeGroupGroupStr : GroupStr (FreeGroup A)
freeGroupGroupStr = groupstr e m inv freeGroupIsGroup

-- FreeGroup is indeed a group
freeGroupGroup : Type ℓ → Group ℓ
freeGroupGroup A = FreeGroup A , freeGroupGroupStr

-- The recursion principle for the FreeGroup
rec : ∀{ℓ'}{Group : Group ℓ'} → {A : Type ℓ} → (A → Group .fst) → GroupHom (freeGroupGroup A) Group
rec {Group = G , (groupstr eg mg invg (isgroup (ismonoid isSemigroupg identityg) inverseg))} {A = A} f = f' , isHom where
  assocg = IsSemigroup.assoc isSemigroupg
  isSetg = IsSemigroup.is-set isSemigroupg
  invrg : ∀ (x : G) → mg x (invg x) ≡ eg
  invrg = λ x → fst (inverseg x)
  invlg : ∀ (x : G) → mg (invg x) x ≡ eg
  invlg = λ x → snd (inverseg x)
  idrg : ∀ (x : G) → x ≡ mg x eg
  idrg = λ x → sym (fst (identityg x))
  idlg : ∀ (x : G) → x ≡ mg eg x
  idlg = λ x → sym (snd (identityg x))
  f' : FreeGroup A → G
  f' (η a)                  = f a
  f' (m g1 g2)              = mg (f' g1) (f' g2)
  f' e                      = eg
  f' (inv g)                = invg (f' g)
  f' (assoc g1 g2 g3 i)     = assocg (f' g1) (f' g2) (f' g3) i
  f' (idr g i)              = idrg (f' g) i
  f' (idl g i)              = idlg (f' g) i
  f' (invr g i)             = invrg (f' g) i
  f' (invl g i)             = invlg (f' g) i
  f' (trunc g1 g2 p q i i₁) = isSetg (f' g1) (f' g2) (cong f' p) (cong f' q) i i₁
  isHom : IsGroupHom freeGroupGroupStr f' _
  isHom = record { pres· = λ x y → refl ; pres1 = refl ; presinv = λ x → refl }

-- The induction principle for the FreeGroup for hProps
elimProp : ∀ {ℓ'}{B : FreeGroup A → Type ℓ'}
         → ((x : FreeGroup A) → isProp (B x))
         → ((a : A) → B (η a))
         → ((g1 g2 : FreeGroup A) → B g1 → B g2 → B (m g1 g2))
         → (B e)
         → ((g : FreeGroup A) → B g → B (inv g))
         → (x : FreeGroup A)
         → B x
elimProp {B = B} Bprop η-ind m-ind e-ind inv-ind = induction where
  induction : ∀ g → B g
  induction (η a) = η-ind a
  induction (m g1 g2) = m-ind g1 g2 (induction g1) (induction g2)
  induction e = e-ind
  induction (inv g) = inv-ind g (induction g)
  induction (assoc g1 g2 g3 i) = path i where
    p1 : B g1
    p1 = induction g1
    p2 : B g2
    p2 = induction g2
    p3 : B g3
    p3 = induction g3
    path : PathP (λ i → B (assoc g1 g2 g3 i)) (m-ind g1 (m g2 g3) p1 (m-ind g2 g3 p2 p3))
                                              (m-ind (m g1 g2) g3 (m-ind g1 g2 p1 p2) p3)
    path = isProp→PathP (λ i → Bprop (assoc g1 g2 g3 i)) (m-ind g1 (m g2 g3) p1 (m-ind g2 g3 p2 p3))
                                                         (m-ind (m g1 g2) g3 (m-ind g1 g2 p1 p2) p3)
  induction (idr g i) = path i where
    p : B g
    p = induction g
    pe : B e
    pe = induction e
    path : PathP (λ i → B (idr g i)) p (m-ind g e p pe)
    path = isProp→PathP (λ i → Bprop (idr g i)) p (m-ind g e p pe)
  induction (idl g i) = path i where
    p : B g
    p = induction g
    pe : B e
    pe = induction e
    path : PathP (λ i → B (idl g i)) p (m-ind e g pe p)
    path = isProp→PathP (λ i → Bprop (idl g i)) p (m-ind e g pe p)
  induction (invr g i) = path i where
    p : B g
    p = induction g
    pinv : B (inv g)
    pinv = inv-ind g p
    pe : B e
    pe = induction e
    path : PathP (λ i → B (invr g i)) (m-ind g (inv g) p pinv) pe
    path = isProp→PathP (λ i → Bprop (invr g i)) (m-ind g (inv g) p pinv) pe
  induction (invl g i) = path i where
    p : B g
    p = induction g
    pinv : B (inv g)
    pinv = inv-ind g p
    pe : B e
    pe = induction e
    path : PathP (λ i → B (invl g i)) (m-ind (inv g) g pinv p) pe
    path = isProp→PathP (λ i → Bprop (invl g i)) (m-ind (inv g) g pinv p) pe
  induction (trunc g1 g2 q1 q2 i i₁) = square i i₁ where
    p1 : B g1
    p1 = induction g1
    p2 : B g2
    p2 = induction g2
    dq1 : PathP (λ i → B (q1 i)) p1 p2
    dq1 = cong induction q1
    dq2 : PathP (λ i → B (q2 i)) p1 p2
    dq2 = cong induction q2
    square : SquareP (λ i i₁ → B (trunc g1 g2 q1 q2 i i₁))
                {a₀₀ = p1} {a₀₁ = p2} dq1
                {a₁₀ = p1} {a₁₁ = p2} dq2
                (cong induction (refl {x = g1})) (cong induction (refl {x = g2}))
    square = isProp→SquareP (λ i i₁ → Bprop (trunc g1 g2 q1 q2 i i₁))
             (cong induction (refl {x = g1})) (cong induction (refl {x = g2}))
             dq1 dq2

-- Two group homomorphisms from FreeGroup to G are the same if they agree on every a : A
freeGroupHom≡ : ∀{ℓ'}{Group : Group ℓ'}{f g : GroupHom (freeGroupGroup A) Group}
               → ((a : A) → (fst f) (η a) ≡ (fst g) (η a)) → f ≡ g
freeGroupHom≡ {Group = G , GStr} {f = f} {g = g} eqOnA = GroupHom≡ (funExt pointwise) where
  1g : G
  1g = GroupStr.1g GStr
  _·_ : G → G → G
  _·_ = GroupStr._·_ GStr
  invg : G → G
  invg = GroupStr.inv GStr
  B : ∀ x → Type _
  B x = (fst f) x ≡ (fst g) x
  Bprop : ∀ x → isProp (B x)
  Bprop x = (isSetGroup (G , GStr)) ((fst f) x) ((fst g) x)
  η-ind : ∀ a → B (η a)
  η-ind = eqOnA
  m-ind : ∀ g1 g2 → B g1 → B g2 → B (m g1 g2)
  m-ind g1 g2 ind1 ind2 =
    (fst f) (m g1 g2)
    ≡⟨ IsGroupHom.pres· (f .snd) g1 g2 ⟩
    ((fst f) g1) · ((fst f) g2)
    ≡⟨ cong (λ x → x · ((fst f) g2)) ind1 ⟩
    ((fst g) g1) · ((fst f) g2)
    ≡⟨ cong (λ x → ((fst g) g1) · x) ind2 ⟩
    ((fst g) g1) · ((fst g) g2)
    ≡⟨ sym (IsGroupHom.pres· (g .snd) g1 g2) ⟩
    (fst g) (m g1 g2) ∎
  e-ind : B e
  e-ind =
    (fst f) e
    ≡⟨ IsGroupHom.pres1 (f .snd) ⟩
    1g
    ≡⟨ sym (IsGroupHom.pres1 (g .snd)) ⟩
    (fst g) e ∎
  inv-ind : ∀ x → B x → B (inv x)
  inv-ind x ind =
    (fst f) (inv x)
    ≡⟨ IsGroupHom.presinv (f .snd) x ⟩
    invg ((fst f) x)
    ≡⟨ cong invg ind ⟩
    invg ((fst g) x)
    ≡⟨ sym (IsGroupHom.presinv (g .snd) x) ⟩
    (fst g) (inv x) ∎
  pointwise : ∀ x → (fst f) x ≡ (fst g) x
  pointwise = elimProp Bprop η-ind m-ind e-ind inv-ind

A→Group≃GroupHom : ∀{ℓ'}{Group : Group ℓ'} → (A → Group .fst) ≃ GroupHom (freeGroupGroup A) Group
A→Group≃GroupHom {Group = Group} = biInvEquiv→Equiv-right (biInvEquiv rec inverse rhomotopy inverse lhomotopy) where
  inverse : GroupHom (freeGroupGroup A) Group → A → Group .fst
  inverse hom a = (hom .fst) (η a)
  rhomotopy : ∀ hom → rec (inverse hom) ≡ hom
  rhomotopy hom = freeGroupHom≡ (λ a → refl)
  lhomotopy : ∀ f → inverse (rec f) ≡ f
  lhomotopy f = funExt (λ a → refl)
