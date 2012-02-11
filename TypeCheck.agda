-- Exercise 4.1
module TypeCheck where

open import Data.Nat
open import Data.List
open import Data.String
open import Data.Fin hiding (_+_)
open import IO.Primitive
open import Foreign.Haskell

{-# IMPORT Parse #-}

data _∈_ {A : Set}(x : A) : List A → Set where
  hd : ∀ {xs}   → x ∈ (x ∷ xs)
  tl : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

index : ∀ {A}{x : A}{xs} → x ∈ xs → Fin (length xs)
index hd     = zero
index (tl p) = suc (index p)

_!_ : {A : Set}(xs : List A)(n : Fin (length xs)) → A
[]       ! ()
(x ∷ xs) ! zero    = x
(x ∷ xs) ! (suc n) = xs ! n

index-∈ : {A : Set}(xs : List A)(n : Fin (length xs)) → (xs ! n) ∈ xs
index-∈ []       ()
index-∈ (x ∷ xs) zero    = hd
index-∈ (x ∷ xs) (suc n) = tl (index-∈ xs n)

infixr 30 _=>_
data Type : Set where
  ¹    : Type
  _=>_ : Type → Type → Type
{-# COMPILED_DATA Type Parse.Type Parse.One Parse.Arr #-}

data _≠_ : Type → Type → Set where
  ¹≠=>    : ∀ {σ τ : Type} → ¹ ≠ (σ => τ)
  =>≠¹    : ∀ {σ τ : Type} → (σ => τ) ≠ ¹
  _≠=>    : ∀ {σ₁ σ₂ τ : Type} → (σ₁ ≠ σ₂) → (σ₁ => τ) ≠ (σ₂ => τ)
  =>≠_    : ∀ {σ τ₁ τ₂ : Type} → (τ₁ ≠ τ₂) → (σ => τ₁) ≠ (σ => τ₂)
  _=>≠=>_ : ∀ {σ₁ τ₁ σ₂ τ₂ : Type} →
            (σ₁ ≠ σ₂) → (τ₁ ≠ τ₂) → (σ₁ => τ₁) ≠ (σ₂ => τ₂)

data Equal? : Type → Type → Set where
  yes : ∀ {τ} → Equal? τ τ
  no  : ∀ {σ τ} → σ ≠ τ → Equal? σ τ

_=?=_ : (σ τ : Type) → Equal? σ τ
¹          =?= ¹          = yes
¹          =?= (_ => _)   = no ¹≠=>
(_ => _)   =?= ¹          = no =>≠¹
(σ₁ => τ₁) =?= (σ₂ => τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
(σ => τ)   =?= (.σ => .τ) | yes  | yes  = yes
(σ => τ₁)  =?= (.σ => τ₂) | yes  | no p = no (=>≠ p)
(σ₁ => τ)  =?= (σ₂ => .τ) | no p | yes  = no (p ≠=>)
(σ₁ => τ₁) =?= (σ₂ => τ₂) | no p | no q = no (p =>≠=> q)

infixl 80 _$_
data Raw : ℕ → Set where
  var : ∀ {n} → Fin n → Raw n
  _$_ : ∀ {n} → Raw n → Raw n → Raw n
  lam : ∀ {n} → Type → Raw (suc n) → Raw n

Cxt = List Type

data Term (Γ : Cxt) : Type → Set where
  var : ∀ {τ} → τ ∈ Γ → Term Γ τ
  _$_ : ∀ {σ τ} → Term Γ (σ => τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ => τ)

erase : ∀ {Γ τ} → Term Γ τ → Raw (length Γ)
erase (var x)   = var (index x)
erase (t $ u)   = erase t $ erase u
erase (lam σ t) = lam σ (erase t)

data BadTerm (Γ : Cxt) : Set where
  _¹$_ : Term Γ ¹ → Raw (length Γ) → BadTerm Γ
  _≠$_ : ∀ {σ₁ σ₂ τ} → Term Γ (σ₁ => τ) → Term Γ σ₂ → (σ₁ ≠ σ₂) → BadTerm Γ
  _b$_ : BadTerm Γ → Raw (length Γ) → BadTerm Γ
  _$b_ : Raw (length Γ) → BadTerm Γ → BadTerm Γ
  lam  : ∀ σ → BadTerm (σ ∷ Γ) → BadTerm Γ

eraseBad : {Γ : Cxt} → BadTerm Γ → Raw (length Γ)
eraseBad (t ¹$ r)     = erase t $ r
eraseBad ((t ≠$ u) p) = erase t $ erase u
eraseBad (b b$ r)     = eraseBad b $ r
eraseBad (r $b b)     = r $ eraseBad b
eraseBad (lam σ b)    = lam σ (eraseBad b)

data Infer (Γ : Cxt) : Raw (length Γ) → Set where
  ok  : (τ : Type)(t : Term Γ τ) → Infer Γ (erase t)
  bad : (b : BadTerm Γ) → Infer Γ (eraseBad b)

infer : (Γ : Cxt)(e : Raw (length Γ)) → Infer Γ e

infer Γ (var n) = {! !}

infer Γ (t $ u) with infer Γ t
infer Γ (.(eraseBad b) $ e₂) | bad b   = bad (b b$ e₂)
infer Γ (.(erase t₁) $ e₂)   | ok ¹ t₁ = bad (t₁ ¹$ e₂)
infer Γ (.(erase t₁) $ e₂)   | ok (σ => τ) t₁ with infer Γ e₂
infer Γ (.(erase t₁) $ .(eraseBad b))
  | ok (σ => τ) t₁ | bad b  = bad (erase t₁ $b b)
infer Γ (.(erase t₁) $ .(erase t₂))
  | ok (σ => τ) t₁ | ok σ' t₂ with σ =?= σ'
infer Γ (.(erase t₁) $ .(erase t₂))
  | ok (σ => τ) t₁ | ok .σ t₂ | yes  = ok τ (t₁ $ t₂)
infer Γ (.(erase t₁) $ .(erase t₂))
  | ok (σ => τ) t₁ | ok σ' t₂ | no p = bad ((t₁ ≠$ t₂) p)

infer Γ (lam σ e) with infer (σ ∷ Γ) e
infer Γ (lam σ .(erase t))    | ok τ t = ok (σ => τ) (lam σ t)
infer Γ (lam σ .(eraseBad b)) | bad b  = bad (lam σ b)

data Named : Set where
  var : String → Named
  _$_ : Named → Named → Named
  lam : String → Type → Named → Named
{-# COMPILED_DATA Named Parse.Term Parse.Var Parse.App Parse.Lam #-}

postulate prettyTerm : Named → Costring
{-# COMPILED prettyTerm show #-}

postulate parseUserFile : IO Named
{-# COMPILED parseUserFile Parse.parseUserFile #-}

main : IO Unit
main = parseUserFile >>= λ t →
       putStr (prettyTerm t) >>= λ _ →
       putStr (toCostring " : ") >>= λ _ →
       putStrLn (toCostring "type will go here")
