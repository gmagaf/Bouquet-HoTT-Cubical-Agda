{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)

open import WA.WA
open import WA.FreeGroupoid
open import WA.GroupoidIsomorphisms

module WA.CodeWindingLooping where

code : ∀ {ℓ}(A : Type ℓ) → (W A) → Type ℓ
code A base       = (FreeGroupoid A)
code A (loop a i) = pathsInU (η a) i

winding : ∀ {ℓ}(A : Type ℓ) → base ≡ base → (FreeGroupoid A)
winding A l = transport (cong (code A) l) e

looping : ∀ {ℓ}(A : Type ℓ) → (FreeGroupoid A) → base ≡ base
looping A (η a) = loop a
looping A (m (g1 , g2)) = (looping A g1) ∙ (looping A g2)
looping A e = refl
looping A (inv x) = sym (looping A x)
looping A (assoc x y z i) = pathAssoc (looping A x) (looping A y) (looping A z) i
looping A (idr x i) = sym (rUnit (looping A x)) i
looping A (idl x i) = sym (lUnit (looping A x)) i
looping A (invr x i) = rCancel (looping A x) i
looping A (invl x i) = lCancel (looping A x) i
