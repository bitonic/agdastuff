-- Exercise 4.1
module TypeCheck where

open import Data.Nat hiding (_≟_)
open import Data.List
open import Data.String
open import Data.Fin hiding (_+_)
open import Data.Product hiding (map)
open import Data.Bool hiding (_≟_)
open import Data.Empty
open import IO.Primitive
open import Foreign.Haskell
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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

data Named : Set where
  var : String → Named
  _$_ : Named → Named → Named
  lam : String → Type → Named → Named
{-# COMPILED_DATA Named Parse.Term Parse.Var Parse.App Parse.Lam #-}

postulate prettyTerm : Named → Costring
{-# COMPILED prettyTerm show #-}

postulate parseUserFile : IO Named
{-# COMPILED parseUserFile Parse.parseUserFile #-}

data _∈_ {A : Set}(x : A) : List A → Set where
  hd : ∀ {xs}   → x ∈ (x ∷ xs)
  tl : ∀ {xs y} → x ∈ xs → x ∈ (y ∷ xs)

_∉_ : {A : Set}(x : A) → List A → Set
x ∉ xs = ¬ (x ∈ xs)

∷-∉ : {A : Set}{x y : A}{xs : List A} → ¬ (x ≡ y) → (y ∉ xs) → (y ∉ (x ∷ xs))
∷-∉ p₁ p₂ hd      = p₁ refl
∷-∉ p₁ p₂ (tl p₃) = p₂ p₃

empty-∉ : {A : Set}{x : A} → x ∉ []
empty-∉ ()

NameCxt = List String

infixl 80 _$_
data Raw (Γ : NameCxt) : Set where
  var : ∀ {s} → (s ∈ Γ) → Raw Γ
  _$_ : Raw Γ → Raw Γ → Raw Γ
  lam : ∀ s → Type → Raw (s ∷ Γ) → Raw Γ

eraseRaw : ∀ {Γ} → Raw Γ → Named
eraseRaw (var {s} n) = var s
eraseRaw (t $ u)     = eraseRaw t $ eraseRaw u
eraseRaw (lam n σ t) = lam n σ (eraseRaw t)

lookup : (xs : List String) → (x : String) → Dec (x ∈ xs)
lookup []       x = no empty-∉
lookup (x ∷ xs) y with x ≟ y
lookup (x ∷ xs) .x | yes refl = yes hd
lookup (x ∷ xs) y  | no p with lookup xs y
lookup (x ∷ xs) y  | no p₁ | yes p₂ = yes (tl p₂)
lookup (x ∷ xs) y  | no p₁ | no p₂  = no (∷-∉ p₁ p₂)

data BadRaw (Γ : NameCxt) : Set where
  var  : ∀ {s} → (s ∉ Γ) → BadRaw Γ
  _b$_ : BadRaw Γ → Named → BadRaw Γ
  _$b_ : Named → BadRaw Γ → BadRaw Γ
  lam  : ∀ s → Type → BadRaw (s ∷ Γ) → BadRaw Γ

eraseBadRaw : ∀ {Γ} → BadRaw Γ → Named
eraseBadRaw (var {s} p)  = var s
eraseBadRaw (b b$ t)     = eraseBadRaw b $ t
eraseBadRaw (t $b b)     = t $ eraseBadRaw b
eraseBadRaw (lam s ty b) = lam s ty (eraseBadRaw b)

data Convert (Γ : NameCxt) : Named → Set where
  ok  : (t : Raw Γ) → Convert Γ (eraseRaw t)
  bad : (b : BadRaw Γ) → Convert Γ (eraseBadRaw b)

convert : (Γ : NameCxt)(t : Named) → Convert Γ t

convert Γ (var v) with lookup Γ v
convert Γ (var v) | yes p = ok (var p)
convert Γ (var v) | no p  = bad (var p)

convert Γ (t $ u) with convert Γ t
convert Γ (.(eraseBadRaw b) $ e₂) | bad b = bad (b b$ e₂)
convert Γ (.(eraseRaw t₁) $ e₂)   | ok t₁ with convert Γ e₂
convert Γ (.(eraseRaw t₁) $ .(eraseBadRaw b))
  | ok t₁ | bad b = bad (eraseRaw t₁ $b b)
convert Γ (.(eraseRaw t₁) $ .(eraseRaw t₂))
  | ok t₁ | ok t₂ = ok (t₁ $ t₂)

convert Γ (lam s ty t) with convert (s ∷ Γ) t
convert Γ (lam s ty .(eraseRaw t))    | ok t  = ok (lam s ty t)
convert Γ (lam s ty .(eraseBadRaw b)) | bad b = bad (lam s ty b)

Cxt = List (String × Type)

data Term (Γ : Cxt) : Type → Set where
  var : ∀ {τ s} → ((s , τ) ∈ Γ) → Term Γ τ
  _$_ : ∀ {σ τ} → Term Γ (σ => τ) → Term Γ σ → Term Γ τ
  lam : ∀ n σ {τ} → Term ((n , σ) ∷ Γ) τ → Term Γ (σ => τ)

∈-proj₁ : {A : Set}{B : Set}{x : A}{y : B}{xys : List (A × B)} →
          (x , y) ∈ xys → x ∈ (map proj₁ xys)
∈-proj₁ hd     = hd
∈-proj₁ (tl p) = tl (∈-proj₁ p)

eraseTerm : ∀ {Γ τ} → Term Γ τ → Raw (map proj₁ Γ)
eraseTerm (var p)     = var (∈-proj₁ p)
eraseTerm (t $ u)     = eraseTerm t $ eraseTerm u
eraseTerm (lam n σ t) = lam n σ (eraseTerm t)

data BadTerm (Γ : Cxt) : Set where
  _¹$_ : Term Γ ¹ → Raw (map proj₁ Γ) → BadTerm Γ
  _≠$_ : ∀ {σ₁ σ₂ τ} → Term Γ (σ₁ => τ) → Term Γ σ₂ → (σ₁ ≠ σ₂) → BadTerm Γ
  _b$_ : BadTerm Γ → Raw (map proj₁ Γ) → BadTerm Γ
  _$b_ : Raw (map proj₁ Γ) → BadTerm Γ → BadTerm Γ
  lam  : ∀ n σ → BadTerm ((n , σ) ∷ Γ) → BadTerm Γ

eraseBadTerm : {Γ : Cxt} → BadTerm Γ → Raw (map proj₁ Γ)
eraseBadTerm (t ¹$ r)     = eraseTerm t $ r
eraseBadTerm ((t ≠$ u) p) = eraseTerm t $ eraseTerm u
eraseBadTerm (b b$ r)     = eraseBadTerm b $ r
eraseBadTerm (r $b b)     = r $ eraseBadTerm b
eraseBadTerm (lam n σ b)  = lam n σ (eraseBadTerm b)

data Infer (Γ : Cxt) : Raw (map proj₁ Γ) → Set where
  ok  : (τ : Type)(t : Term Γ τ) → Infer Γ (eraseTerm t)
  bad : (b : BadTerm Γ) → Infer Γ (eraseBadTerm b)

keyValue : {A B : Set} → (k : A) (kvs : List (A × B)) →
              k ∈ (map proj₁ kvs) → Σ B (λ v → (k , v) ∈ kvs)
keyValue k []               ()
keyValue k ((.k , v) ∷ kvs) hd     = v , hd
keyValue k ((k' , v) ∷ kvs) (tl p) with keyValue k kvs p
keyValue k ((k' , v) ∷ kvs) (tl p) | (v' , p') = v' , tl p'

infer : (Γ : Cxt)(e : Raw (map proj₁ Γ)) → Infer Γ e

infer Γ (var {s = s} n) with keyValue s Γ n
infer Γ (var {s = s} n) | (τ , p) = {! !} -- ok τ (var p)

infer Γ (t $ u) with infer Γ t
infer Γ (.(eraseBadTerm b) $ e₂) | bad b   = bad (b b$ e₂)
infer Γ (.(eraseTerm t₁) $ e₂)   | ok ¹ t₁ = bad (t₁ ¹$ e₂)
infer Γ (.(eraseTerm t₁) $ e₂)   | ok (σ => τ) t₁ with infer Γ e₂
infer Γ (.(eraseTerm t₁) $ .(eraseBadTerm b))
  | ok (σ => τ) t₁ | bad b  = bad (eraseTerm t₁ $b b)
infer Γ (.(eraseTerm t₁) $ .(eraseTerm t₂))
  | ok (σ => τ) t₁ | ok σ' t₂ with σ =?= σ'
infer Γ (.(eraseTerm t₁) $ .(eraseTerm t₂))
  | ok (σ => τ) t₁ | ok .σ t₂ | yes  = ok τ (t₁ $ t₂)
infer Γ (.(eraseTerm t₁) $ .(eraseTerm t₂))
  | ok (σ => τ) t₁ | ok σ' t₂ | no p = bad ((t₁ ≠$ t₂) p)

infer Γ (lam s σ e) with infer ((s , σ) ∷ Γ) e
infer Γ (lam s σ .(eraseTerm t))    | ok τ t = ok (σ => τ) (lam s σ t)
infer Γ (lam s σ .(eraseBadTerm b)) | bad b  = bad (lam s σ b)

main : IO Unit
main =
  parseUserFile                             >>= λ t →
  putStr (prettyTerm t)                     >>= λ _ →
  putStr (toCostring " : ")                 >>= λ _ →
  putStrLn (toCostring "type will go here")
