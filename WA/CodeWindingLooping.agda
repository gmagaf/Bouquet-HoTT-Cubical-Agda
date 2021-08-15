{-

This file contains:

- Definition of functions of the equivalence between FreeGroup and the FundamentalGroup

-}
{-# OPTIONS --cubical #-}

module WA.WA.CodeWindingLooping where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)
open import Cubical.HITs.SetTruncation
open import Cubical.Algebra.Group

open import WA.WA.Base
open import WA.FreeGroup
open import WA.FreeGroupoid
open import WA.FundamentalGroup


ΩWA : ∀ {ℓ}{A : Type ℓ} → Type ℓ
ΩWA {A = A} = Ω {A = W A} {base = base}

-- Functions without using the truncated forms of types

looping : ∀ {ℓ}{A : Type ℓ} → FreeGroupoid A → ΩWA
looping (η a)              = loop a
looping (m g1 g2)          = looping g1 ∙ looping g2
looping e                  = refl
looping (inv g)            = sym (looping g)
looping (assoc g1 g2 g3 i) = pathAssoc (looping g1) (looping g2) (looping g3) i
looping (idr g i)          = rUnit (looping g) i
looping (idl g i)          = lUnit (looping g) i
looping (invr g i)         = rCancel (looping g) i
looping (invl g i)         = lCancel (looping g) i

code : ∀ {ℓ}{A : Type ℓ} → (W A) → Type ℓ
code {A = A} base = (FreeGroupoid A)
code (loop a i)   = pathsInU (η a) i

winding : ∀ {ℓ}{A : Type ℓ} → ΩWA → FreeGroupoid A
winding l = subst code l e

-- Functions using the truncated forms of types

π₁WAGroup : ∀ {ℓ}{A : Type ℓ} → Group ℓ
π₁WAGroup {A = A} = π₁Group {A = W A} {base = base}

π₁WA : ∀ {ℓ}{A : Type ℓ} → Type ℓ
π₁WA {A = A} = π₁WAGroup {A = A} .fst

loopingT : ∀ {ℓ}{A : Type ℓ} → ∥ FreeGroupoid A ∥₂ → π₁WA
loopingT = map looping

windingT : ∀ {ℓ}{A : Type ℓ} → π₁WA → ∥ FreeGroupoid A ∥₂
windingT = map winding
