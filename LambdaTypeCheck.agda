-- Exercise 4.1
module LambdaTypeCheck where

open import Data.Nat
open import Data.List
open import Data.String
open import IO.Primitive
open import Foreign.Haskell

{-# IMPORT LambdaParse #-}

data _∈_ {A : Set}(x : A) : List A → Set where
  hd : ∀ {xs}   → x ∈ (x ∷ xs)
  tl : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

index : ∀ {A}{x : A}{xs} → x ∈ xs → ℕ
index hd     = zero
index (tl p) = suc (index p)

data Lookup {A : Set}(xs : List A) : ℕ → Set where
  inside  : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : ℕ) → Lookup xs n
[]       ! n    = outside n
(x ∷ xs) ! zero = inside x hd
(x ∷ xs) ! suc n with xs ! n
(x ∷ xs) ! suc .(index p)       | inside y p = inside y (tl p)
(x ∷ xs) ! suc .(length xs + n) | outside n  = outside n

infixr 30 _=>_
data Type : Set where
  ¹    : Type
  _=>_ : Type → Type → Type
{-# COMPILED_DATA Type LambdaParse.Type LambdaParse.One LambdaParse.Arr #-}

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
data Raw : Set where
  var : ℕ → Raw
  _$_ : Raw → Raw → Raw
  lam : Type → Raw → Raw

Cxt = List Type

data Term (Γ : Cxt) : Type → Set where
  var : ∀ {τ} → τ ∈ Γ → Term Γ τ
  _$_ : ∀ {σ τ} → Term Γ (σ => τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ => τ)

erase : ∀ {Γ τ} → Term Γ τ → Raw
erase (var x)   = var (index x)
erase (t $ u)   = erase t $ erase u
erase (lam σ t) = lam σ (erase t)

data BadTerm (Γ : Cxt) : Set where
  var  : (n : ℕ) → BadTerm Γ
  _¹$_ : Term Γ ¹ → Raw → BadTerm Γ
  _≠$_ : ∀ {σ₁ σ₂ τ} → Term Γ (σ₁ => τ) → Term Γ σ₂ → (σ₁ ≠ σ₂) → BadTerm Γ
  _b$_ : BadTerm Γ → Raw → BadTerm Γ
  _$b_ : Raw → BadTerm Γ → BadTerm Γ
  lam  : ∀ σ → BadTerm (σ ∷ Γ) → BadTerm Γ

eraseBad : {Γ : Cxt} → BadTerm Γ → Raw
eraseBad {Γ} (var n)  = var (length Γ + n)
eraseBad (t ¹$ r)     = erase t $ r
eraseBad ((t ≠$ u) p) = erase t $ erase u
eraseBad (b b$ r)     = eraseBad b $ r
eraseBad (r $b b)     = r $ eraseBad b
eraseBad (lam σ b)    = lam σ (eraseBad b)

data Infer (Γ : Cxt) : Raw → Set where
  ok  : (τ : Type)(t : Term Γ τ) → Infer Γ (erase t)
  bad : (b : BadTerm Γ) → Infer Γ (eraseBad b)

infer : (Γ : Cxt)(e : Raw) → Infer Γ e

infer Γ (var n) with Γ ! n
infer Γ (var .(length Γ + n)) | outside n  = bad (var n)
infer Γ (var .(index x))      | inside σ x = ok σ (var x)

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

data NamedTerm : Set where
  var : String → NamedTerm
  _$_ : NamedTerm → NamedTerm → NamedTerm
  lam : String → Type → NamedTerm → NamedTerm
{-# COMPILED_DATA NamedTerm LambdaParse.Term LambdaParse.Var LambdaParse.App LambdaParse.Lam #-}

postulate prettyTerm : NamedTerm → Costring
{-# COMPILED prettyTerm show #-}

postulate parseUserFile : IO NamedTerm
{-# COMPILED parseUserFile LambdaParse.parseUserFile #-}

main : IO Unit
main = parseUserFile >>= λ t →
       putStr (prettyTerm t) >>= λ _ →
       putStr (toCostring " : ") >>= λ _ →
       putStrLn (toCostring "type will go here")
