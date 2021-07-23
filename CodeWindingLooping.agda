{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.HITs.SetTruncation

open import WA.WA
open import WA.FreeGroup
open import WA.GroupoidIsomorphisms
open import WA.FundamentalGroup

module WA.CodeWindingLooping where

ΩWA : ∀ {ℓ}{A : Type ℓ} → Type ℓ
ΩWA {A = A} = Ω {A = W A} {base = base}

π₁WA : ∀ {ℓ}{A : Type ℓ} → Type ℓ
π₁WA {A = A} = π₁ {A = W A} {base = base}

code : ∀ {ℓ}{A : Type ℓ} → (W A) → Type ℓ
code {A = A} base = (FreeGroup A)
code (loop a i)   = pathsInU (η a) i

winding : ∀ {ℓ}{A : Type ℓ} → (π₁WA) → (FreeGroup A)
winding {A = A} = rec freeGroupIsSet inductionBase where
  inductionBase : ΩWA → FreeGroup A
  inductionBase l = transport (cong code l) e

looping : ∀ {ℓ}{A : Type ℓ} → (FreeGroup A) → π₁WA
looping (η a)                  = ∣ loop a ∣₂
looping (m (g1 , g2))          = concLoops (looping g1) (looping g2)
looping e                      = idLoop
looping (inv x)                = invLoop (looping x)
looping (assoc x y z i)        = assocLoops (looping x) (looping y) (looping z) i
looping (idr x i)              = rUnitLoop (looping x) i
looping (idl x i)              = lUnitLoop (looping x) i
looping (invr x i)             = rCancelLoop (looping x) i
looping (invl x i)             = lCancelLoop (looping x) i
looping (trunc g1 g2 p q i i₁) = squash₂ (looping g1) (looping g2) (cong looping p) (cong looping q) i i₁
