{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws hiding(assoc)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base

module WA.FreeGroup where

private
  variable
    ℓ : Level

data FreeGroup (A : Type ℓ) : Type ℓ where
  η : A → FreeGroup A
  m : FreeGroup A → FreeGroup A → FreeGroup A
  e : FreeGroup A
  inv : FreeGroup A → FreeGroup A
  assoc : ∀ x y z → m x (m y z) ≡ m (m x y) z
  idr : ∀ x → x ≡ m x e
  idl : ∀ x → x ≡  m e x
  invr : ∀ x → m x (inv x) ≡ e
  invl : ∀ x → m (inv x) x ≡ e
  trunc : ∀ x y → ∀ (p q : x ≡ y) → p ≡ q

freeGroupIsSet : {A : Type ℓ} → isSet (FreeGroup A)
freeGroupIsSet = trunc

freeGroupIsSemiGroup : {A : Type ℓ} → IsSemigroup {A = FreeGroup A} m
freeGroupIsSemiGroup = issemigroup freeGroupIsSet assoc

freeGroupIsMonoid : {A : Type ℓ} → IsMonoid {A = FreeGroup A} e m
freeGroupIsMonoid = ismonoid freeGroupIsSemiGroup (λ x → sym (idr x) , sym (idl x))

freeGroupIsGroup : {A : Type ℓ} → IsGroup {G = FreeGroup A} e m inv
freeGroupIsGroup = isgroup freeGroupIsMonoid (λ x → invr x , invl x)

freeGroupGroupStr : {A : Type ℓ} → GroupStr (FreeGroup A)
freeGroupGroupStr = groupstr e m inv freeGroupIsGroup

freeGroupGroup : Type ℓ → Group ℓ
freeGroupGroup A = FreeGroup A , freeGroupGroupStr

rec : ∀{ℓ'}{Group : Group ℓ'} → {A : Type ℓ} → (A → Group .fst) → GroupHom (freeGroupGroup A) Group
rec {Group = G , GStr} {A = A} f = f' , isHom where
  eg : G
  eg = GroupStr.1g GStr
  mg : G → G → G
  mg = GroupStr._·_ GStr
  invg : G → G
  invg = GroupStr.inv GStr
  isGroupg = GroupStr.isGroup GStr
  isMonoidg = IsGroup.isMonoid isGroupg
  isSemigroupg = IsMonoid.isSemigroup isMonoidg
  assocg = IsSemigroup.assoc isSemigroupg
  inverseg = IsGroup.inverse isGroupg
  identityg = IsMonoid.identity isMonoidg
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
  isHom : IsGroupHom freeGroupGroupStr f' GStr
  isHom = record { pres· = λ x y → refl ; pres1 = refl ; presinv = λ x → refl }

elimProp : ∀ {ℓ'}{A : Type ℓ}{B : FreeGroup A → Type ℓ'}
         → ((x : FreeGroup A) → isProp (B x))
         → ((a : A) → B (η a))
         → ((g1 g2 : FreeGroup A) → B g1 → B g2 → B (m g1 g2))
         → (B e)
         → ((g : FreeGroup A) → B g → B (inv g))
         → (x : FreeGroup A)
         → B x
elimProp {A = A} {B = B} Bprop η-ind m-ind e-ind inv-ind = induction where
  induction : (g : FreeGroup A) → B g
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
