{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws

open import WA.WA
open import WA.FreeGroupoid
open import WA.GroupoidIsomorphisms

module WA.Code_Winding where

code : ∀ {ℓ}(A : Type ℓ) → (W A) → Type ℓ
code A base       = (FreeGroupoid A)
code A (loop a i) = pathsInU a i

winding : ∀ {ℓ}(A : Type ℓ) → base ≡ base → (FreeGroupoid A)
winding A l = transport (cong (code A) l) e

looping : ∀ {ℓ}(A : Type ℓ) → (FreeGroupoid A) → base ≡ base
looping A (η a) = loop a
looping A (m (g1 , g2)) = (looping A g1) ∙ (looping A g2)
looping A e = refl
looping A (inv x) = sym (looping A x)
looping A (FreeGroupoid.assoc x y z i) = Cubical.Foundations.GroupoidLaws.assoc (looping A x) (looping A y) (looping A z) i
looping A (idr x i) = sym (rUnit (looping A x)) i
looping A (idl x i) = sym (lUnit (looping A x)) i
looping A (invr x i) = rCancel (looping A x) i
looping A (invl x i) = lCancel (looping A x) i

-- lhomotopy : ∀ {ℓ}(A : Type ℓ) → ∀ (g : FreeGroupoid A) → winding A (looping A g) ≡ g
-- lhomotopy A (η a) =
--   winding A (looping A (η a))
--   ≡⟨ refl ⟩
--   transport (ua (equivs a)) e
--   ≡⟨ uaβ (equivs a) e ⟩
--   equivFun (equivs a) e
--   ≡⟨ refl ⟩
--   automorhpism a e
--   ≡⟨ refl ⟩
--   m(η a , e)
--   ≡⟨ idr (η a) ⟩
--   η a ∎
-- lhomotopy A (m (g1 , g2)) =
--   winding A (looping A (m (g1 , g2)))
--   ≡⟨ refl ⟩
--   winding A ((looping A g1) ∙ (looping A g2))
--   ≡⟨ refl ⟩
--   transport (cong (code A) ((looping A g1) ∙ (looping A g2))) e
--   ≡⟨ cong (λ p → transport p e) (cong-∙ (code A) (looping A g1) (looping A g2)) ⟩
--   transport ((cong (code A) (looping A g1)) ∙ (cong (code A) (looping A g2))) e
--   ≡⟨ refl ⟩
--   transport (cong (code A) (looping A g2)) (transport (cong (code A) (looping A g1)) e)
--   ≡⟨ refl ⟩
--   transport (cong (code A) (looping A g2)) (winding A (looping A g1))
--   ≡⟨ cong (λ p → transport (cong (code A) (looping A g2)) p) (lhomotopy A g1) ⟩
--   transport (cong (code A) (looping A g2)) g1
--   ≡⟨ refl ⟩
--   m (g1 , g2) ∎
