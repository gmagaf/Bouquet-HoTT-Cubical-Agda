{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)

open import WA.WA
open import WA.FreeGroupoid
open import WA.GroupoidIsomorphisms

module WA.CodeWindingLooping where

code : ∀ {ℓ}{A : Type ℓ} → (W A) → Type ℓ
code {A = A} base = (FreeGroupoid A)
code (loop a i)   = pathsInU (η a) i

winding : ∀ {ℓ}{A : Type ℓ} → base ≡ base → (FreeGroupoid A)
winding l = transport (cong code l) e

looping : ∀ {ℓ}{A : Type ℓ} → (FreeGroupoid A) → base ≡ base
looping (η a)           = loop a
looping (m (g1 , g2))   = (looping g1) ∙ (looping g2)
looping e               = refl
looping (inv x)         = sym (looping x)
looping (assoc x y z i) = pathAssoc (looping x) (looping y) (looping z) i
looping (idr x i)       = rUnit (looping x) i
looping (idl x i)       = lUnit (looping x) i
looping (invr x i)      = rCancel (looping x) i
looping (invl x i)      = lCancel (looping x) i
