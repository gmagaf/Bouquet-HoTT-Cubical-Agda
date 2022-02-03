{-

This file contains:

- Definition of functions of the equivalence between FreeGroup and the FundamentalGroup

-}
{-# OPTIONS --cubical #-}

module Bouquet.Bouquet.CodeWindingLooping where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)
open import Cubical.HITs.SetTruncation
open import Cubical.Algebra.Group

open import Bouquet.Bouquet.Base
open import Bouquet.FreeGroup
open import Bouquet.FreeGroupoid
open import Bouquet.FundamentalGroup

private
  variable
    ℓ : Level
    A : Type ℓ

ΩBouquet : {A : Type ℓ} → Type ℓ
ΩBouquet {A = A} = Ω {A = Bouquet A} {base = base}

-- Functions without using the truncated forms of types

looping : FreeGroupoid A → ΩBouquet
looping (η a)              = loop a
looping (m g1 g2)          = looping g1 ∙ looping g2
looping e                  = refl
looping (inv g)            = sym (looping g)
looping (assoc g1 g2 g3 i) = pathAssoc (looping g1) (looping g2) (looping g3) i
looping (idr g i)          = rUnit (looping g) i
looping (idl g i)          = lUnit (looping g) i
looping (invr g i)         = rCancel (looping g) i
looping (invl g i)         = lCancel (looping g) i

code : {A : Type ℓ} → (Bouquet A) → Type ℓ
code {A = A} base = (FreeGroupoid A)
code (loop a i)   = pathsInU (η a) i

winding : ΩBouquet → FreeGroupoid A
winding l = subst code l e

-- Functions using the truncated forms of types

π₁BouquetGroup : {A : Type ℓ} → Group ℓ
π₁BouquetGroup {A = A} = π₁Group {A = Bouquet A} {base = base}

π₁Bouquet : {A : Type ℓ} → Type ℓ
π₁Bouquet {A = A} = π₁BouquetGroup {A = A} .fst

loopingT : ∥ FreeGroupoid A ∥₂ → π₁Bouquet
loopingT = map looping

windingT : π₁Bouquet → ∥ FreeGroupoid A ∥₂
windingT = map winding
