module Quicksort where

open import Function
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_; _>_)
                     renaming (_≟_ to _ℕ≟_)
open import Data.Nat.Properties using (≤-step)
open import Data.List hiding (filter)
open import Data.Sum
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
                      renaming (_≟_ to _Bool≟_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
            using (_≡_; _≢_; refl; inspect; cong) renaming ([_] to [_]≡)
open import Relation.Nullary using (¬_; yes; no)

infixr 2 _×_
infix 3 _⇔_

record Product (A : Set) (B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

_×_ : (A B : Set) → Set
_×_ = Product

_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)

lesseq : ℕ → ℕ → Bool
lesseq 0       _       = true
lesseq (suc n) 0       = false
lesseq (suc n) (suc m) = lesseq n m

greater : ℕ → ℕ → Bool
greater n = not ∘ lesseq n

lesseq₁ = flip lesseq
greater₁ = flip greater

eq : ℕ → ℕ → Bool
eq n m = lesseq n m ∧ lesseq m n

filter : {A : Set} → (A → Bool) → List A → List A
filter _ []       = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false = filter p xs

length-filter : {A : Set} (n : ℕ) (xs : List A)
                (p₁ : length xs ≤ n)
                (p₂ : A → Bool) → (length (filter p₂ xs) ≤ n)
length-filter n       []       p₁       p₂ = z≤n
length-filter 0       (_ ∷ _)  ()       p₂
length-filter (suc n) (x ∷ xs) (s≤s p₁) p₂ with p₂ x
... | true  = s≤s (length-filter n xs p₁ p₂)
... | false = ≤-step (length-filter n xs p₁ p₂)

qsort₁ : (n : ℕ) (l : List ℕ) → (length l ≤ n) → List ℕ
qsort₁ n       []       p = []
qsort₁ 0       (_ ∷ _)  ()
qsort₁ (suc n) (x ∷ xs) (s≤s p) =
  qsort₁ n (filter (lesseq₁ x) xs) (length-filter n xs p (lesseq₁ x)) ++
  [ x ] ++
  qsort₁ n (filter (greater₁ x) xs) (length-filter n xs p (greater₁ x))

≤-refl : {n : ℕ} → n ≤ n
≤-refl {0}     = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

qsort : List ℕ → List ℕ
qsort xs = qsort₁ (length xs) xs ≤-refl

sorted : List ℕ → Set
sorted []            = ⊤
sorted (x ∷ xs) with xs
sorted (x ∷ xs) | y ∷ ys = (x ≤ y) × sorted xs
sorted (x ∷ xs) | []     = ⊤

occs : ℕ → List ℕ → ℕ
occs _ []       = 0
occs n (m ∷ ns) with eq n m
... | true  = 1 + occs n ns
... | false = occs n ns

mem : {A : Set} → A → List A → Set
mem _ []       = ⊥
mem n (m ∷ ns) = (n ≡ m) ⊎ mem n ns

perm : List ℕ → List ℕ → Set
perm l₁ l₂ = ∀ (n : ℕ) → occs n l₁ ≡ occs n l₂

sorted₁ : (l m : List ℕ) (a : ℕ) →
          sorted l → sorted m →
          ((b : ℕ) → mem b l → b ≤ a) →
          ((b : ℕ) → mem b m → a ≤ b) →
          sorted (l ++ [ a ] ++ m)
sorted₁ []      []      a sl         sm a≥l a≤m = _
sorted₁ []      (n ∷ m) a sl         sm a≥l a≤m = a≤m n (inj₁ refl) , sm
sorted₁ (n ∷ l) m       a sl         sm a≥l a≤m with l
sorted₁ (n ∷ l) m       a (n≤b , sl) sm a≥l a≤m | (b ∷ l') =
  n≤b , sorted₁ (b ∷ l') m a sl sm (λ x → a≥l x ∘ inj₂) a≤m
sorted₁ (n ∷ l) m       a ⊤          sm a≥l a≤m | []       =
  a≥l n (inj₁ refl) , sorted₁ [] m a _ sm (λ _ → ⊥-elim) a≤m

lesseq-≤ : (x y : ℕ) → (lesseq x y ≡ true) → x ≤ y
lesseq-≤ zero    y       refl = z≤n
lesseq-≤ (suc x) zero    ()
lesseq-≤ (suc x) (suc y) p    = s≤s (lesseq-≤ x y p)

lesseq-⊎-greater : (x y : ℕ) → (lesseq x y ≡ true ⊎ greater x y ≡ true)
lesseq-⊎-greater zero    y       = inj₁ refl
lesseq-⊎-greater (suc x) zero    = inj₂ refl
lesseq-⊎-greater (suc x) (suc y) = lesseq-⊎-greater x y

¬-lesseq-×-greater : (x y : ℕ) → ¬ (lesseq x y ≡ true × greater x y ≡ true)
¬-lesseq-×-greater zero    y       (_ , ())
¬-lesseq-×-greater (suc x) zero    (() , _)
¬-lesseq-×-greater (suc x) (suc y) p        = ¬-lesseq-×-greater x y p

mem-filter : (p : ℕ → Bool) (l : List ℕ) (x : ℕ) → mem x (filter p l) →
             p x ≡ true
mem-filter p []      x  ()
mem-filter p (y ∷ l) x  m with p y | inspect p y
mem-filter p (y ∷ l) .y (inj₁ refl) | true  | [ eq ]≡ = eq
mem-filter p (y ∷ l) x  (inj₂ ml)   | true  | _       = mem-filter p l x ml
mem-filter p (y ∷ l) x  m           | false | _       = mem-filter p l x m

mem-filter-lesseq : (l : List ℕ) (a x : ℕ) →
                    mem x (filter (lesseq₁ a) l) → x ≤ a
mem-filter-lesseq l a x p = lesseq-≤ x a (mem-filter (lesseq₁ a) l x p)

≡-pred : ∀ {n m} → suc n ≡ suc m → n ≡ m
≡-pred refl = refl

¬eq-≢ : ∀ {n m} → (eq n m) ≡ false → n ≢ m
¬eq-≢ {zero}  {zero}  () _
¬eq-≢ {zero}  {suc n} p  ()
¬eq-≢ {suc n} {zero}  p  ()
¬eq-≢ {suc n} {suc m} p₁ p₂ with eq n m | inspect (eq n) m
¬eq-≢ {suc n} {suc m} () p₂ | true  | _
¬eq-≢ {suc n} {suc m} p₁ p₂ | false | [ eq ]≡ = (¬eq-≢ eq) (≡-pred p₂)

eq-≡ : ∀ {n m b} → (eq n m) ≡ b → if b then n ≡ m else n ≢ m
eq-≡ {zero}  {zero}  {true}_    = refl
eq-≡ {zero}  {suc n} {true}  ()
eq-≡ {suc n} {zero}  {true}  ()
eq-≡ {suc n} {suc m} {true}  p with eq n m | inspect (eq n) m
eq-≡ {suc n} {suc m} {true}  p  | true  | [ eq ]≡ = cong suc (eq-≡ eq)
eq-≡ {suc n} {suc m} {true}  () | false | _
eq-≡ {n}     {m}     {false} p = ¬eq-≢ p

mem-occs : (x : ℕ) (l : List ℕ) → (mem x l ⇔ occs x l > 0)
mem-occs x []      = ⊥-elim , λ()
mem-occs n (m ∷ l) with eq n m | inspect (eq n) m
mem-occs n (m ∷ l) | true  | [ eq ]≡ = const (s≤s z≤n) , const (inj₁ (eq-≡ eq))
mem-occs n (m ∷ l) | false | [ eq ]≡ =
  (λ { (inj₁ eq₁)   → ⊥-elim (eq-≡ eq eq₁)
     ; (inj₂ memnl) → Product.proj₁ (mem-occs n l) memnl}) ,
  λ occs>0 → inj₂ (Product.proj₂ (mem-occs n l) occs>0)

perm-mem : (l l' : List ℕ) → perm l l' → (x : ℕ) → (mem x l ⇔ mem x l')
perm-mem l l' p x = {! !}

occs-++ : (a : ℕ) (l m : List ℕ) → (occs a (l ++ m) ≡ occs a l + occs a m)
occs-++ a l m = {! !}

perm-++₁ : (l m x : List ℕ) (a : ℕ) → perm (l ++ m) x →
           perm (l ++ [ a ] ++ m) (a ∷ x)
perm-++₁ l m x a p = {! !}

perm-++₂ : (l l' m m' : List ℕ) → perm l l' × perm m m' → perm (l ++ m) (l' ++ m')
perm-++₂ l l' m m' (pl , pm) = {! !}

perm-filter : (l : List ℕ) (a : ℕ) →
              perm l (filter (lesseq₁ a) l ++ filter (greater₁ a) l)
perm-filter l a = {! !}

qsort₁-sorted : (m : ℕ) (l : List ℕ) (p : length l ≤ m) →
                (sorted (qsort₁ m l p) × perm l (qsort₁ m l p))
qsort₁-sorted 0       []      p       = _ , λ _ → refl
qsort₁-sorted 0       (_ ∷ _) ()
qsort₁-sorted (suc m) []      p       = _ , λ _ → refl
qsort₁-sorted (suc m) (a ∷ l) (s≤s p) = {! !}

qsort-sorted : (xs : List ℕ) → sorted (qsort xs)
qsort-sorted xs = {! !}

qsort-perm : (xs : List ℕ) → perm xs (qsort xs)
qsort-perm xs = {! !}
