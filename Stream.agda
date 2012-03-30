module Stream where

open import Coinduction
open import Data.Nat
open import Relation.Nullary
open import Data.Bool using (Bool; true; false)

infixr 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

map : ∀ {A B} → (A → B) → Stream A → Stream B
map f (x ∷ xs) = f x ∷ ♯ (map f (♭ xs))

iterate : ∀ {A} → (A → A) → A → Stream A
iterate f st = st ∷ ♯ (iterate f (f st))

infold : ∀ {A B} → (B → A → B) → B → Stream A → Stream B
infold f st (x ∷ xs) = st ∷ ♯ (infold f (f st x) (♭ xs))

ones : Stream ℕ
ones = 1 ∷ ♯ ones

nats : Stream ℕ
nats = iterate (_+_ 1) 0

_!_ : ∀ {A} → Stream A → ℕ → A
(x ∷ _)  ! 0       = x
(_ ∷ xs) ! (suc n) = (♭ xs) ! n

-- Merge two ordered lists free of duplicates
merge : Stream ℕ → Stream ℕ → Stream ℕ
merge (x ∷ xs) (y ∷ ys) with x ≟ y | x ≤? y
... | yes _ | _     = x ∷ ♯ (merge (♭ xs) (♭ ys))
... | no _  | yes _ = x ∷ ♯ (merge (♭ xs) (y ∷ ys))
... | no _  | no _  = y ∷ ♯ (merge (x ∷ xs) (♭ ys))

hammings : Stream ℕ
hammings = let twos   = iterate (_*_ 2) 1
               threes = iterate (_*_ 3) 1
               fives  = iterate (_*_ 5) 1
           in  merge twos (merge threes fives)

