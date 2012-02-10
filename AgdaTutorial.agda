module AgdaTutorial where

apply : (A : Set)(B : A → Set) → ((x : A) → B x) → (a : A) → B a
apply A B f a = f a

_∘_ : {A : Set}{B : A → Set}{C : (x : A) → B x → Set}
      (f : {x : A}(y : B x) → C x y)(g : (x : A) → B x)
      (x : A) → C x (g x)
(f ∘ g) x = f (g x)

module Bool where
  data Bool : Set where
    true  : Bool
    false : Bool

  not : Bool → Bool
  not true  = false
  not false = true

module Nat where
  open Bool

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero  + m = m
  suc n + m = suc (n + m)

  _×_ : ℕ → ℕ → ℕ
  zero     × _ = zero
  suc zero × m = m
  suc n    × m = n + (n × m)

  identity : (A : Set) → A → A
  identity A x = x

  zero' : ℕ
  zero' = identity ℕ zero

  plus-two = suc ∘ suc

  _<_ : ℕ → ℕ → Bool
  _     < zero  = false
  zero  < suc n = true
  suc m < suc n = m < n

module BoolTypes where
  open Bool

  data   False : Set where
  record True  : Set where

  trivial : True
  trivial = _

  isTrue : Bool → Set
  isTrue true  = True
  isTrue false = False

module List where
  open Nat
  open Bool
  open BoolTypes

  infixr 40 _∷_

  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  _++_ : {A : Set} → List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  length : {A : Set} → List A → ℕ
  length []       = zero
  length (x ∷ xs) = suc (length xs)

  lookup : {A : Set}(xs : List A)(n : ℕ) → isTrue (n < length xs) → A
  lookup []       n       ()
  lookup (x ∷ xs) zero    _  = x
  lookup (x ∷ xs) (suc n) p  = lookup xs n p

  map : {A B : Set} → (A → B) → List A → List B
  map f []        = []
  map f (x ∷ xs) = f x ∷ map f xs

  filter : {A : Set} → (A → Bool) → List A → List A
  filter _ [] = []
  filter p (x ∷ xs) with p x
  ... | true  = x ∷ filter p xs
  ... | false = filter p xs

  infix 20 _⊆_
  data _⊆_ {A : Set} : List A → List A → Set where
    stop : [] ⊆ []
    drop : ∀ {xs y ys} → xs ⊆ ys →     xs ⊆ y ∷ ys
    keep : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys

  lem-filter : {A : Set}(p : A → Bool)(xs : List A) → filter p xs ⊆ xs
  lem-filter p [] = stop
  lem-filter p (x ∷ xs) with p x
  ... | true  = keep (lem-filter p xs)
  ... | false = drop (lem-filter p xs)

module Fin where
  open Nat

  data Fin : ℕ → Set where
    fzero : {n : ℕ} → Fin (suc n)
    fsuc  : {n : ℕ} → Fin n → Fin (suc n)

  data Empty : Set where
    empty : Fin zero → Empty

module Vec where
  open Nat
  open Fin

  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

  head : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
  head (x ∷ xs) = xs

  vmap : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
  vmap _ []       = []
  vmap f (x ∷ xs) = f x ∷ vmap f xs

  _!_ : {n : ℕ}{A : Set} → Vec A n → Fin n → A
  []       ! ()
  (x ∷ xs) ! fzero    = x
  (x ∷ xs) ! (fsuc i) = xs ! i

  tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
  tabulate {zero}  f = []
  tabulate {suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

data Image_∋_ {A B : Set}(f : A → B) : B → Set where
  im : (x : A) → Image f ∋ f x

inv : {A B : Set}(f : A → B)(y : B) → Image f ∋ y → A
inv f .(f x) (im x) = x

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ {x : A} → x ≡ x

module EqTypes where
  open Nat
  open BoolTypes

  data _≤_ : ℕ → ℕ → Set where
    leq-zero : {n : ℕ} → zero ≤ n
    leq-suc  : {m n : ℕ} → m ≤ n → suc m ≤ suc n

  leq-trans : {l m n : ℕ} → l ≤ m → m ≤ n → l ≤ n
  leq-trans leq-zero    _           = leq-zero
  leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)

  data _≠_ : ℕ → ℕ → Set where
    z≠s : {n : ℕ} → zero ≠ suc n
    s≠z : {n : ℕ} → suc n ≠ zero
    s≠s : {m n : ℕ} → m ≠ n → suc m ≠ suc n

  data Equal? (n m : ℕ) : Set where
    eq  : n ≡ m → Equal? n m
    neq : n ≠ m → Equal? n m

  equal? : (n m : ℕ) → Equal? n m
  equal? zero    zero    = eq refl
  equal? zero    (suc m) = neq z≠s
  equal? (suc m) zero    = neq s≠z
  equal? (suc n) (suc m) with equal? n m
  equal? (suc n) (suc .n) | eq refl = eq refl
  equal? (suc n) (suc m)  | neq p   = neq (s≠s p)

module Maybe where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just    : A → Maybe A

  maybe : {A B : Set} → B → (A → B) → Maybe A → B
  maybe z f nothing  = z
  maybe z f (just x) = f x

module Sort (A : Set)(_<_ : A → A → Bool.Bool) where
  open List
  open Bool

  insert : A → List A → List A
  insert y [] = y ∷ []
  insert y (x ∷ xs) with x < y
  ... | true  = x ∷ insert y xs
  ... | false = y ∷ x ∷ xs

  sort : List A → List A
  sort []        = []
  sort (x ∷ xs) = insert x (sort xs)

module Sortℕ = Sort Nat.ℕ Nat._<_

module Lists (A : Set)(_<_ : A → A → Bool.Bool) where
  open List
  open Sort A _<_ public
  open Maybe
  minimum : List A → Maybe A
  minimum xs with sort xs
  ... | []      = nothing
  ... | y ∷ ys = just y

record Point : Set where
  open Nat

  field x : ℕ
        y : ℕ

  mkPoint : ℕ → ℕ → Point
  mkPoint a b = record{x = a; y = b}

record Monad (M : Set → Set) : Set1 where
  open List

  field
    return : {A : Set} → A → M A
    _>>=_  : {A B : Set} → M A → (A → M B) → M B

  mapM : {A B : Set} → (A → M B) → List A → M (List B)
  mapM f []        = return []
  mapM f (x ∷ xs) = f x       >>= \y →
                     mapM f xs >>= \ys →
                     return (y ∷ ys)

module Exercise2-1 where
  open Vec
  open Nat

  Matrix : Set → ℕ → ℕ → Set
  Matrix A n m = Vec (Vec A n) m

  vec : {n : ℕ}{A : Set} → A → Vec A n
  vec {zero}  _ = []
  vec {suc n} x = x ∷ vec {n} x

  infixl 90 _$_
  _$_ : {n : ℕ}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
  []       $ []       = []
  (f ∷ fs) $ (x ∷ xs) = f x ∷ fs $ xs

  transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
  transpose []         = vec []
  transpose (xs ∷ xss) = vmap (\x xs → x ∷ xs) xs $ transpose xss

module Exercise2-2 where
  open Vec
  open Fin

  lem-!-tab : ∀ {A n} (f : Fin n → A)(i : Fin n) → (tabulate f ! i) ≡ f i
  lem-!-tab f fzero    = refl
  lem-!-tab f (fsuc i) = lem-!-tab (f ∘ fsuc) i

  vec-∷-≡ : ∀ {A n} {xs : Vec A n}{ys : Vec A n}{x : A} →
            xs ≡ ys → (x ∷ xs) ≡ (x ∷ ys)
  vec-∷-≡ refl = refl

  lem-tab-! : ∀ {A n} (xs : Vec A n) → tabulate (_!_ xs) ≡ xs
  lem-tab-! []       = refl
  lem-tab-! (x ∷ xs) = vec-∷-≡ (lem-tab-! xs)

module Exercise2-3 where
  open List
  open Bool

  ⊆-refl : {A : Set}{xs : List A} → xs ⊆ xs
  ⊆-refl {xs = []}     = stop
  ⊆-refl {xs = x ∷ xs} = keep (⊆-refl {xs = xs})

  ⊆-trans : {A : Set}{xs ys zs : List A} →
            xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
  ⊆-trans stop     stop     = stop
  ⊆-trans p        (drop q) = drop (⊆-trans p q)
  ⊆-trans (drop p) (keep q) = drop (⊆-trans p q)
  ⊆-trans (keep p) (keep q) = keep (⊆-trans p q)

  infixr 30 _∷_
  data SubList {A : Set} : List A → Set where
    []   : SubList []
    _∷_  : ∀ x {xs} → SubList xs → SubList (x ∷ xs)
    skip : ∀ {x xs} → SubList xs → SubList (x ∷ xs)

  forget : {A : Set}{xs : List A} → SubList xs → List A
  forget []        = []
  forget (x ∷ xs)  = x ∷ forget xs
  forget (skip xs) = forget xs

  lem-forget : {A : Set}{xs : List A}(zs : SubList xs) →
               forget zs ⊆ xs
  lem-forget []        = stop
  lem-forget (x ∷ xs)  = keep (lem-forget xs)
  lem-forget (skip xs) = drop (lem-forget xs)

  filter' : {A : Set} → (A → Bool) → (xs : List A) → SubList xs
  filter' p []       = []
  filter' p (x ∷ xs) with p x
  ... | true  = x ∷ filter' p xs
  ... | false = skip (filter' p xs)

  complement : {A : Set}{xs : List A} → SubList xs → SubList xs
  complement []                = []
  complement (x ∷ xs)          = skip (complement xs)
  complement (skip {x = x} xs) = x ∷ complement xs

  sublists : {A : Set}(xs : List A) → List (SubList xs)
  sublists []       = [] ∷ []
  sublists (x ∷ xs) = let s = sublists xs
                      in  map skip s ++ map (_∷_ x) s

module Views where
  open import Data.Nat

  _×_ : ℕ → ℕ → ℕ
  _×_ = _*_

  data Parity : ℕ → Set where
    even : (k : ℕ) → Parity (k × 2)
    odd  : (k : ℕ) → Parity (1 + k × 2)

  parity : (n : ℕ) → Parity n
  parity zero = even zero
  parity (suc n) with parity n
  parity (suc .(k × 2))     | even k = odd k
  parity (suc .(1 + k × 2)) | odd k  = even (suc k)

  half : ℕ → ℕ
  half n with parity n
  half .(k × 2)     | even k = k
  half .(1 + k × 2) | odd k  = k

  open import Data.List
  open import Data.Bool renaming (T to isTrue)

  isFalse : Bool → Set
  isFalse b = isTrue (not b)

  infixr 30 _:all:_
  data All {A : Set}(P : A → Set) : List A → Set where
    all[]   : All P []
    _:all:_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

  satisfies : {A : Set} → (A → Bool) → A → Set
  satisfies p x = isTrue (p x)

  data Find {A : Set}(p : A → Bool) : List A → Set where
    found     : (xs : List A)(y : A) → satisfies p y → (ys : List A) →
                Find p (xs ++ y ∷ ys)
    not-found : ∀ {xs} → All (satisfies (not ∘ p)) xs → Find p xs

  data Inspect {A : Set}(x : A) : Set where
    it : (y : A) → x ≡ y → Inspect x

  inspect : {A : Set}(x : A) → Inspect x
  inspect x = it x refl

  trueIsTrue : {x : Bool} → x ≡ true → isTrue x
  trueIsTrue refl = _

  falseIsFalse : {x : Bool} → x ≡ false → isFalse x
  falseIsFalse refl = _

  find : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
  find p [] = not-found all[]
  find p (x ∷ xs) with inspect (p x)
  ... | it true prf = found [] x (trueIsTrue prf) xs
  ... | it false prf with find p xs
  find p (x ∷ ._) | it false _   | found xs y py ys =
    found (x ∷ xs) y py ys
  find p (x ∷ xs) | it false prf | not-found npxs =
    not-found (falseIsFalse prf :all: npxs)

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

module Lambda where
  open import Data.Nat
  open import Data.List
  open Views

  infixr 30 _=>_
  data Type : Set where
    ¹    : Type
    _=>_ : Type → Type → Type
  {-# COMPILED_DATA Type Type One Arr #-}

  data Equal? : Type → Type → Set where
    yes : ∀ {τ} → Equal? τ τ
    no  : ∀ {σ τ} → Equal? σ τ

  _=?=_ : (σ τ : Type) → Equal? σ τ
  ¹          =?= ¹          = yes
  ¹          =?= (_ => _)   = no
  (_ => _)   =?= ¹          = no
  (σ₁ => τ₁) =?= (σ₂ => τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
  (σ => τ)   =?= (.σ => .τ) | yes | yes = yes
  (σ₁ => τ₁) =?= (σ₂ => τ₂) | _   | _   = no

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

  data Infer (Γ : Cxt) : Raw → Set where
    ok  : (τ : Type)(t : Term Γ τ) → Infer Γ (erase t)
    bad : {e : Raw} → Infer Γ e

  infer : (Γ : Cxt)(e : Raw) → Infer Γ e

  infer Γ (var n) with Γ ! n
  infer Γ (var .(length Γ + n)) | outside n = bad
  infer Γ (var .(index x))      | inside σ x = ok σ (var x)

  infer Γ (t $ u) with infer Γ t
  infer Γ (t $ u)            | bad     = bad
  infer Γ (.(erase t₁) $ e₂) | ok ¹ t₁ = bad
  infer Γ (.(erase t₁) $ e₂) | ok (σ => τ) t₁ with infer Γ e₂
  infer Γ (.(erase t₁) $ e₂)          | ok (σ => τ) t₁ | bad = bad
  infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ => τ) t₁ | ok σ' t₂ with σ =?= σ'
  infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ => τ) t₁ | ok .σ t₂ | yes =
    ok τ (t₁ $ t₂)
  infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ => τ) t₁ | ok σ' t₂ | no  = bad

  infer Γ (lam σ e) with infer (σ ∷ Γ) e
  infer Γ (lam σ .(erase t)) | ok τ t = ok (σ => τ) (lam σ t)
  infer Γ (lam σ e)          | bad    = bad

module Exercises3-1 where
  open Nat

  data Compare : ℕ → ℕ → Set where
    less : ∀ {n} k → Compare n (n + suc k)
    more : ∀ {n} k → Compare (n + suc k) n
    same : ∀ {n} → Compare n n

  compare : (n m : ℕ) → Compare n m
  compare zero    zero   = same
  compare zero    (suc m) = less m
  compare (suc n) zero    = more n
  compare (suc n) (suc m) with compare n m
  compare (suc n)            (suc .n)           | same   = same
  compare (suc n)            (suc .(n + suc k)) | less k = less k
  compare (suc .(m + suc k)) (suc m)            | more k = more k

  difference : ℕ → ℕ → ℕ
  difference n m with compare n m
  difference n            .n           | same   = zero
  difference n            .(n + suc k) | less k = zero
  difference .(m + suc k) m            | more k = suc k

module Exercises3-2 where
  open import Data.Nat
  open import Data.List
  open Views

  infixr 30 _=>_
  data Type : Set where
    ¹    : Type
    _=>_ : Type → Type → Type

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

module Exercises3-3 where
  open Views
  open import Data.Bool
  open import Data.List

  lemma-All-∈ : ∀ {A x xs}{P : A → Set} → All P xs → x ∈ xs → P x
  lemma-All-∈ all[]        ()
  lemma-All-∈ (p :all: xs) hd     = p
  lemma-All-∈ (p :all: xs) (tl i) = lemma-All-∈ xs i

  lem-filter-sound : {A : Set}(p : A → Bool)(xs : List A) →
                     All (satisfies p) (filter p xs)
  lem-filter-sound p [] = all[]
  lem-filter-sound p (x ∷ xs) with inspect (p x)
  lem-filter-sound p (x ∷ xs) | it y prf with p x | prf
  lem-filter-sound p (x ∷ xs) | it .true prf  | true  | refl =
    trueIsTrue prf :all: lem-filter-sound p xs
  lem-filter-sound p (x ∷ xs) | it .false prf | false | refl =
    lem-filter-sound p xs

module Exercises3-4 where
  open import Data.List hiding (_++_)
  open import Data.Nat
  open import Data.String
  open import Data.Bool
  open Views

  True : Set
  True = T true

  False : Set
  False = T false

  Tag = String

  mutual
    data Schema : Set where
      tag : Tag → List Child → Schema

    data Child : Set where
      text : Child
      elem : ℕ → ℕ → Schema → Child

  data BList (A : Set) : ℕ → Set where
    []  : ∀ {n} → BList A n
    _∷_ : ∀ {n} → A → BList A n → BList A (suc n)

  data Cons (A B : Set) : Set where
    _∷_ : A → B → Cons A B

  FList : Set → ℕ → ℕ → Set
  FList A zero    m       = BList A m
  FList A (suc n) zero    = False
  FList A (suc n) (suc m) = Cons A (FList A n m)

  mutual
    data XML : Schema → Set where
      element : ∀ {kids}(t : Tag) → All Element kids → XML (tag t kids)

    Element : Child → Set
    Element text         = String
    Element (elem n m s) = FList (XML s) n m

  mutual
    printXML : {s : Schema} → XML s → String
    printXML (element t kids) =
      "<" ++ t ++ ">" ++ printChildren kids ++ "</" ++ t ++ ">"

    printChildren : {kids : List Child} → All Element kids → String
    printChildren                  all[]           = ""
    printChildren {text ∷ _}       (s :all: kids)  = s
    printChildren {elem n m s ∷ _} (fl :all: kids) = printFList n m fl

    printFList : {s : Schema}(n m : ℕ) → FList (XML s) n m → String
    printFList {s} (suc n) zero    ()
    printFList {s} (zero)  m       bl         = printBList bl
    printFList {s} (suc n) (suc m) (xml ∷ fl) = printXML xml ++ printFList n m fl

    printBList : {s : Schema}{n : ℕ} → BList (XML s) n → String
    printBList []         = ""
    printBList (xml ∷ bl) = printXML xml ++ printBList bl

module Exercises4-1 where
  open Exercises3-2
  open import Data.String

  data NamedTerm : Set where
    var : String → NamedTerm
    _$_ : NamedTerm → NamedTerm → NamedTerm
    lam : String → Type → NamedTerm → NamedTerm
  -- {-# COMPILED_DATA NamedTerm Term Var App Lam #-}

  data Unit : Set where
    unit : Unit
  {-# COMPILED_DATA Unit () () #-}

  postulate IO : Set → Set
  {-# COMPILED_TYPE IO IO #-}

  postulate
    return : {A : Set} → A → IO A
    _>>=_  : {A B : Set} → (A → IO B) → IO B

  {-# COMPILED return (\a → return) #-}
  {-# COMPILED _>>=_  (\a b → (>>=)) #-}
