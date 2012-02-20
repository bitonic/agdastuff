module Stack where

import Data.List as List
open List using (List; []; _∷_; _++_)
import Data.Nat as Nat
open Nat using (ℕ; zero; suc; _+_)
open import Function
open import Data.Bool

data Stack : List Set → Set₁ where
  []  : Stack []
  _∷_ : {A : Set} {ts : List Set} → (x : A) → Stack ts → Stack (A ∷ ts)

head : ∀ {A ts} → Stack (A ∷ ts) → A
head (x ∷ xs) = x

infixl 1 _=>_

_=>_ : (ts₁ ts₂ : List Set) → Set₁
ts₁ => ts₂ = Stack ts₁ → Stack ts₂

push : ∀ {A ts} → (x : A) → ts => A ∷ ts
push = _∷_

dup : ∀ {A ts} → A ∷ ts => A ∷ A ∷ ts
dup (x ∷ xs) = x ∷ x ∷ xs

swap : ∀ {A B ts} → A ∷ B ∷ ts => B ∷ A ∷ ts
swap (x ∷ y ∷ xs) = y ∷ x ∷ xs

lift1 : ∀ {A B ts} → (A → B) → A ∷ ts => B ∷ ts
lift1 f (x ∷ xs) = f x ∷ xs

lift2 : ∀ {A B C ts} → (A → B → C) → A ∷ B ∷ ts => C ∷ ts
lift2 f (x ∷ y ∷ xs) = f x y ∷ xs

add : ∀ {ts} → ℕ ∷ ℕ ∷ ts => ℕ ∷ ts
add (x ∷ y ∷ xs) = (x + y) ∷ xs

infixr 1 _>>_

_>>_ : ∀ {a b c} → (a => b) → (b => c) → a => c
_>>_ a b = b ∘ a

test : ∀ {ts} → ts => ℕ ∷ ts
test = push 1 >> push 2 >> add

dropℕ : ∀ {ts} → (n : ℕ) → ts => List.drop n ts
dropℕ zero    xs       = xs
dropℕ (suc n) []       = []
dropℕ (suc n) (x ∷ xs) = dropℕ n xs

drop : ∀ {ts} → (s : Stack (ℕ ∷ ts)) → Stack (List.drop (head s) ts)
drop (n ∷ xs) = dropℕ n xs

then_else_ : ∀ {ts} {f : Bool → List Set} →
             (ts => f true) → (ts => f false) →
             (s : Stack (Bool ∷ ts)) → Stack (f (head s))
then_else_ t e (true  ∷ s) = t s
then_else_ t e (false ∷ s) = e s

test2 : ∀ {ts x y} → (x ∷ y ∷ ts) => ts
test2 = drop ∘ add ∘ push 3 ∘ push 1 ∘ push 2 ∘ push 3
