module Telescope where

open import Function
open import Level
open import Data.Maybe
open import Data.Unit
open import Data.Product

module AdHoc₁ where
  data Σ₁ (A : Set) (B : A → Set) : Set₁ where
    _,_ : (x : A) → B x → Σ₁ A B

  data Σ₂ (A : Set)
          (B : A → Set)
          (C : (x : A) → B x → Set) :
          Set₁ where
    _,_,_ : (x : A) → (y : B x) → C x y → Σ₂ A B C

  data Σ₃ (A : Set)
          (B : A → Set)
          (C : (x : A) → B x → Set)
          (D : (x : A) → (y : B x) → C x y → Set) :
          Set₁ where
    _,_,_,_ : (x : A) → (y : B x) → (z : C x y) → (D x y z) → Σ₃ A B C D


module AdHoc₂ where
  Σ₂ : (A : Set) (B : A → Set) (C : (x : A) → B x → Set) → Set
  Σ₂ A B C = Σ A (λ x → Σ (B x) (C x))

  Σ₃ : (A : Set)
       (B : A → Set)
       (C : (x : A) → B x → Set)
       (D : (x : A) → (y : B x) → C x y → Set)
       → Set
  Σ₃ A B C D = Σ A (λ x → Σ₂ (B x) (C x) (D x))

  Σ₄ : (A : Set)
       (B : A → Set)
       (C : (x : A) → B x → Set)
       (D : (x : A) → (y : B x) → C x y → Set)
       (E : (x : A) → (y : B x) → (z : C x y) → D x y z → Set)
       → Set
  Σ₄ A B C D E = Σ A (λ x → Σ₃ (B x) (C x) (D x) (E x))

mutual
  infixl 5 _▻_

  data Telescope : Set₁ where
    ε   : Telescope
    _▻_ : (t : Telescope) → ([ t ] → Set) → Telescope

  [_] : Telescope → Set
  [ ε ]     = ⊤
  [ t ▻ f ] = Σ [ t ] f

Σ₀ : (A : Set) → Telescope
Σ₀ A = ε ▻ (λ ⊤ → A)

Σ₁ : (A : Set) (B : A → Set) → Telescope
Σ₁ A B = Σ₀ A ▻ (B ∘ Σ.proj₂)

Σ₂ : (A : Set) (B : A → Set) (C : (x : A) → B x → Set) → Telescope
Σ₂ A B C = Σ₁ A B ▻ (λ s → C (Σ.proj₂ (Σ.proj₁ s)) (Σ.proj₂ s))

Σ₃ : (A : Set)
     (B : A → Set)
     (C : (x : A) → B x → Set)
     (D : (x : A) → (y : B x) → C x y → Set)
     → Telescope
Σ₃ A B C D = Σ₂ A B C ▻ (λ s → D (Σ.proj₂ (Σ.proj₁ (Σ.proj₁ s)))
                                 (Σ.proj₂ (Σ.proj₁ s))
                                 (Σ.proj₂ s))
