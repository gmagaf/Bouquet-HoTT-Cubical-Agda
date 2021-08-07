{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.HITs.SetTruncation renaming (rec to recTrunc)
open import Cubical.Algebra.Group

open import WA.WA
open import WA.FreeGroup
open import WA.GroupIsomorphisms
open import WA.FundamentalGroup

module WA.CodeWindingLooping where

ΩWA : ∀ {ℓ}{A : Type ℓ} → Type ℓ
ΩWA {A = A} = Ω {A = W A} {base = base}

π₁WAGroup : ∀ {ℓ}{A : Type ℓ} → Group ℓ
π₁WAGroup {A = A} = π₁Group {A = W A} {base = base}

π₁WA : ∀ {ℓ}{A : Type ℓ} → Type ℓ
π₁WA {A = A} = π₁WAGroup {A = A} .fst

loopingHom : ∀ {ℓ}{A : Type ℓ} → GroupHom (freeGroupGroup A) π₁WAGroup
loopingHom {A = A} =
  let f : A → π₁WA
      f a = ∣ loop a ∣₂
  in rec f

looping : ∀ {ℓ}{A : Type ℓ} → FreeGroup A → π₁WA
looping = loopingHom .fst

code : ∀ {ℓ}{A : Type ℓ} → (W A) → Type ℓ
code {A = A} base = (FreeGroup A)
code (loop a i)   = pathsInU (η a) i

encode : ∀ {ℓ}{A : Type ℓ} → (x : W A) → base ≡ x → code x
encode x l = subst code l e

winding : ∀ {ℓ}{A : Type ℓ} → π₁WA → FreeGroup A
winding = recTrunc freeGroupIsSet (λ l → subst code l e)

-- TODO fix this as an homomorphism
-- windingHom : ∀ {ℓ}{A : Type ℓ} → GroupHom π₁WAGroup (freeGroupGroup A)
-- windingHom {A = A} = hom , isHom where
  -- f : ΩWA → FreeGroup A
  -- f l = subst code l e
--   f' : FreeGroup A → ΩWA → FreeGroup A
--   f' g l = subst code l g
--   wanted : (l : ΩWA) → (g : FreeGroup A) → f' g l ≡ m g (f' e l)
--   wanted l g = J P d l where
--     P : (x : W A) → (base ≡ x) → Type _
--     P x l = subst code l g ≡ (subst (λ x → code x → code x) l (m g)) (subst code l e)
--     postulate d : P base refl
--   -- elimProp Bprop η-ind m-ind e-ind inv-ind g where
--   --   B : FreeGroup A → Type _
--   --   B g = f' g l ≡ m g (f' e l)
--   --   Bprop : ∀ g → isProp (f' g l ≡ m g (f' e l))
--   --   Bprop g = freeGroupIsSet (f' g l) (m g (f' e l))
--   --   η-ind : (a : A) → B (η a)
--   --   η-ind a =
--   --     subst code l (η a)
--   --     ≡⟨ {!   !} ⟩
--   --     m (η a) (f' e l) ∎
--     -- postulate m-ind : (g1 g2 : FreeGroup A) → B g1 → B g2 → B (m g1 g2)
--     -- postulate e-ind : B e
--     -- postulate inv-ind : (g : FreeGroup A) → B g → B (inv g)
--   hom : π₁WA → FreeGroup A
--   hom = recTrunc freeGroupIsSet f
--   pres· : (p q : π₁WA) → hom (∙-π₁ p q) ≡ m (hom p) (hom q)
--   pres· p q = elim sethood ind p where
--     postulate sethood : (p' : π₁WA) → isSet (hom (∙-π₁ p' q) ≡ m (hom p') (hom q))
--     ind : (l1 : ΩWA) → hom (∙-π₁ ∣ l1 ∣₂ q) ≡ m (hom ∣ l1 ∣₂) (hom q)
--     ind l1 = elim sethood' ind' q where
--       postulate sethood' : (q' : π₁WA) → isSet (hom (∙-π₁ ∣ l1 ∣₂ q') ≡ m (hom ∣ l1 ∣₂) (hom q'))
--       ind' : (l2 : ΩWA) → hom (∙-π₁ ∣ l1 ∣₂ ∣ l2 ∣₂) ≡ m (hom ∣ l1 ∣₂) (hom ∣ l2 ∣₂)
--       ind' l2 =
--         hom (∙-π₁ ∣ l1 ∣₂ ∣ l2 ∣₂)
--         ≡⟨ refl ⟩
--         hom ∣ l1 ∙ l2 ∣₂
--         ≡⟨ refl ⟩
--         f (l1 ∙ l2)
--         ≡⟨ refl ⟩
--         subst code (l1 ∙ l2) e
--         ≡⟨ substComposite code l1 l2 e ⟩
--         subst code l2 (subst code l1 e)
--         ≡⟨ refl ⟩
--         subst code l2 (f l1)
--         ≡⟨ refl ⟩
--         f' (f l1) l2
--         ≡⟨ wanted l2 (f l1) ⟩
--         m (f l1) (subst code l2 e)
--         ≡⟨ refl ⟩
--         m (f l1) (f l2)
--         ≡⟨ refl ⟩
--         m (hom ∣ l1 ∣₂) (hom ∣ l2 ∣₂) ∎
--   pres1 : hom 1π₁ ≡ e
--   pres1 = refl
--   postulate presinv : (p : π₁WA) → hom (invπ₁ p) ≡ inv (hom p)
--   isHom : IsGroupHom π₁GroupStr hom freeGroupGroupStr
--   isHom = record { pres· = pres· ; pres1 = pres1 ; presinv = presinv }
