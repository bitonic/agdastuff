module W where

open import Function
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty

data W (A : Set)(B : A → Set) : Set₁ where
  node : (a : A) → (B a → W A B) → W A B

Tree : (A : Set) → Set₁
Tree A = W (⊤ ⊎ A) f
  where
    f : (⊤ ⊎ A) → Set
    f (inj₁ _) = ⊥
    f (inj₂ _) = (⊤ ⊎ ⊤)

null : ∀ {A} → Tree A
null = node (inj₁ _) ⊥-elim

branch : ∀ {A} → (a : A) → Tree A → Tree A → Tree A
branch x l r = node (inj₂ x) [(λ _ → l) , (λ _ → r)]

List : (A : Set) → Set₁
List A = W (⊤ ⊎ A) f
  where
    f : (⊤ ⊎ A) → Set
    f (inj₁ _) = ⊥
    f (inj₂ _) = ⊤

[] : ∀ {A} → List A
[] = node (inj₁ _) ⊥-elim

_∷_ : ∀ {A} → (a : A) → List A → List A
x ∷ l = node (inj₂ x) (λ _ → l)

[_] : ∀ {A} → (a : A) → List A
[ x ] = x ∷ []

infixl 50 _++_
_++_ : ∀ {A} → List A → List A → List A
(node (inj₁ _) _) ++ r = r
(node (inj₂ x) f) ++ r = x ∷ (f _ ++ r)

flatten : ∀ {A} → Tree A → List A
flatten (node (inj₁ _) _) = []
flatten (node (inj₂ x) f) =
  flatten (f (inj₁ _)) ++ [ x ] ++ flatten (f (inj₂ _))

-- Salmon!
map : ∀ {A B} → (A → B) → Tree A → Tree B
map f (node (inj₂ x) g) = node (inj₂ (f x)) (map f ∘ g)
map f t                 = null
