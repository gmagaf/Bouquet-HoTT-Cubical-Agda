{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod.Base

module WA.FreeGroupoid where

private
  variable
    ℓ : Level

data FreeGroupoid (A : Type ℓ) : Type ℓ where
  η : A → FreeGroupoid A
  m : FreeGroupoid A × FreeGroupoid A → FreeGroupoid A
  e : FreeGroupoid A
  inv : FreeGroupoid A → FreeGroupoid A
  assoc : ∀ x y z → m(x , m(y , z)) ≡ m(m(x , y) , z)
  idr : ∀ x → m(x , e) ≡ x
  idl : ∀ x → m(e , x) ≡ x
  invr : ∀ x → m(x , inv x) ≡ e
  invl : ∀ x → m(inv x , x) ≡ e
