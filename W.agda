module W where

open import Function
open import Data.Unit
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; Σ; proj₁; proj₂; _,_)

data W (A : Set)(B : A → Set) : Set₁ where
  node : (a : A) → (B a → W A B) → W A B

syntax W A (λ x → B) = W[ x ∶ A ] B

rec : {S : Set} {P : S → Set}
      (C : W S P → Set) →      -- some conclusion we hope holds
      ((s : S) →               -- given a shape…
       (f : P s → W S P) →     -- …and a bunch of kids…
       ((p : P s) → C (f p)) → -- …and C for each kid in the bunch…
       C (node s f)) →         -- …does C hold for the node?
      (x : W S P) →            -- If so,…
      C x                      -- … C always holds.
rec C c (node s f) = c s f (λ p → rec C c (f p))

module Me where
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
  
  -- Bool : Set₁
  -- Bool = W (⊤ ⊎ ⊤) (λ _ → ⊥)
  
  -- true : Bool
  -- true = node (inj₁ _) ⊥-elim

  -- false : Bool
  -- false = node (inj₂ _) ⊥-elim

module Conor where
  Tr : Bool → Set
  Tr true  = ⊤
  Tr false = ⊥
  
  Nat : Set₁
  Nat = W Bool Tr
  
  zero : Nat
  zero = node false λ()
  
  suc : Nat → Nat
  suc n = node true (λ _ → n)
  
  LW : (A : Set) (LP : A → Set × Set) → Set₁
  LW S LP = W (Σ S (proj₁ ∘ LP)) (proj₂ ∘ LP ∘ proj₁)

  List : Set → Set₁
  List X = LW Bool (λ {true → (X , ⊤); false → (⊤ , ⊥)})

  [] : ∀ {A} → List A
  [] = node (false , tt) λ()

  _∷_ : ∀ {A} → A → List A → List A
  x ∷ xs = node (true , x) (const xs)

  indNat : (C : Nat → Set)               -- some conclusion we hope holds
           (zc : C zero)                 -- does C hold for zero?
           ((n : Nat) → C n → C (suc n)) -- does C respect suc?
           (n : Nat) → C n               -- If so, C always holds.
  indNat = {! !}