module TypeCheck where

open import Data.List
open import Data.String
open import Data.Product
open import IO.Primitive
open import Foreign.Haskell
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary

{-# IMPORT Parse #-}

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

data Raw : Set where
  var : String → Raw
  _$_ : Raw → Raw → Raw
  lam : String → Type → Raw → Raw
{-# COMPILED_DATA Raw Parse.Term Parse.Var Parse.App Parse.Lam #-}

postulate prettyTerm : Raw → Costring
{-# COMPILED prettyTerm show #-}

postulate parseUserFile : IO Raw
{-# COMPILED parseUserFile Parse.parseUserFile #-}

Map : (A B : Set) → Set
Map A B = List (A × B)

data _∈_ {A B : Set}(k : A) : Map A B → Set where
  hd : ∀ {xs v} → k ∈ ((k , v) ∷ xs)
  tl : ∀ {xs k' v} → k' ≢ k → k ∈ xs → k ∈ ((k' , v) ∷ xs)

_∉_ : {A B : Set}(x : A) → Map A B → Set
k ∉ xs = ¬ (k ∈ xs)

∷-∉ : {A B : Set}{k₁ k₂ : A}{v : B}{xs : Map A B} → (k₁ ≢ k₂) →
      (k₂ ∉ xs) → (k₂ ∉ ((k₁ , v) ∷ xs))
∷-∉ p₁ p₂ hd        = p₁ refl
∷-∉ p₁ p₂ (tl e p₃) = p₂ p₃

empty-∉ : {A B : Set}{k : A} → (_∉_ {A} {B} k [])
empty-∉ ()

Cxt = Map String Type

lookup : (Γ : Cxt)(s : String) →  Dec (s ∈ Γ)
lookup []            s = no (empty-∉)
lookup ((s , τ) ∷ Γ) s' with s ≟ s'
lookup ((s , τ) ∷ Γ) .s | yes refl = yes hd
lookup ((s , τ) ∷ Γ) s' | no p with lookup Γ s'
lookup ((s , τ) ∷ Γ) s' | no p₁ | yes p₂ = yes (tl p₁ p₂)
lookup ((s , τ) ∷ Γ) s' | no p₁ | no p₂  = no (∷-∉ p₁ p₂)

value : {A B : Set} → (xs : Map A B) → {k : A} → k ∈ xs → B
value []             ()
value ((k , v) ∷ xs) hd       = v
value (_ ∷ xs)       (tl _ p) = value xs p

data Term (Γ : Cxt) : Type → Set where
  var : ∀ {s} → (p : s ∈ Γ) → Term Γ (value Γ p)
  _$_ : ∀ {σ τ} → Term Γ (σ => τ) → Term Γ σ → Term Γ τ
  lam : ∀ n σ {τ} → Term ((n , σ) ∷ Γ) τ → Term Γ (σ => τ)

erase : ∀ {Γ τ} → Term Γ τ → Raw
erase (var {s} p) = var s
erase (t $ u)     = erase t $ erase u
erase (lam s σ t) = lam s σ (erase t)

data BadTerm (Γ : Cxt) : Set where
  var  : ∀ {s} → (s ∉ Γ) → BadTerm Γ
  _¹$_ : Term Γ ¹ → Raw  → BadTerm Γ
  _≠$_ : ∀ {σ₁ σ₂ τ} → Term Γ (σ₁ => τ) → Term Γ σ₂ → (σ₁ ≠ σ₂) → BadTerm Γ
  _b$_ : BadTerm Γ → Raw → BadTerm Γ
  _$b_ : Raw → BadTerm Γ → BadTerm Γ
  lam  : ∀ s σ → BadTerm ((s , σ) ∷ Γ) → BadTerm Γ

eraseBad : {Γ : Cxt} → BadTerm Γ → Raw
eraseBad (var {s} p)  = var s
eraseBad (t ¹$ r)     = erase t $ r
eraseBad ((t ≠$ u) p) = erase t $ erase u
eraseBad (b b$ r)     = eraseBad b $ r
eraseBad (r $b b)     = r $ eraseBad b
eraseBad (lam n σ b)  = lam n σ (eraseBad b)

data Infer (Γ : Cxt) : Raw → Set where
  ok  : (τ : Type)(t : Term Γ τ) → Infer Γ (erase t)
  bad : (b : BadTerm Γ) → Infer Γ (eraseBad b)

infer : (Γ : Cxt)(e : Raw) → Infer Γ e

infer Γ (var s) with lookup Γ s
infer Γ (var s) | yes p = ok (value Γ p) (var p)
infer Γ (var s) | no p  = bad (var p)

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

infer Γ (lam s σ e) with infer ((s , σ) ∷ Γ) e
infer Γ (lam s σ .(erase t))    | ok τ t = ok (σ => τ) (lam s σ t)
infer Γ (lam s σ .(eraseBad b)) | bad b  = bad (lam s σ b)

main : IO Unit
main =
  parseUserFile                             >>= λ t →
  putStr (prettyTerm t)                     >>= λ _ →
  putStr (toCostring " : ")                 >>= λ _ →
  putStrLn (toCostring "type will go here")
