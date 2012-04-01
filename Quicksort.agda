module Quicksort where

import Level
open import Function
open import Data.Nat
            using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_; _>_; pred)
            renaming (_≟_ to _ℕ≟_)
open import Data.Nat.Properties using (≤-step)
open import Data.List hiding (filter)
open import Data.Sum
open import Data.Bool
            using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
            renaming (_≟_ to _Bool≟_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
            using (_≡_; _≢_; refl; inspect; cong; sym; subst; trans)
            renaming ([_] to [_]≡)
open import Relation.Nullary using (¬_; yes; no)

infixr 2 _×_
infix 3 _⇔_

record Prod (A : Set) (B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

_×_ : (A B : Set) → Set
_×_ = Prod

_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)

_lesseq_ : ℕ → ℕ → Bool
0 lesseq       _       = true
(suc n) lesseq 0       = false
(suc n) lesseq (suc m) = n lesseq m

_greater_ : ℕ → ℕ → Bool
_greater_ n = not ∘ _lesseq_ n

lesseq₁ = flip _lesseq_
greater₁ = flip _greater_

eq : ℕ → ℕ → Bool
eq n m = n lesseq m ∧ m lesseq n

eq-suc : (m n : ℕ) → eq m n ≡ true → eq (suc m) (suc n) ≡ true
eq-suc zero    zero    _ = refl
eq-suc zero    (suc _) ()
eq-suc (suc _) zero    ()
eq-suc (suc m) (suc n) p = eq-suc m n p

≡→eq : (m n : ℕ) → m ≡ n → eq m n ≡ true
≡→eq zero     zero    _ = refl
≡→eq zero    (suc _) ()
≡→eq (suc _) zero    ()
≡→eq (suc m) (suc n) p  = eq-suc m n (≡→eq m n (cong pred p))

filter : {A : Set} → (A → Bool) → List A → List A
filter _ []       = []
filter p (x ∷ l) with p x
...              | true  = x ∷ filter p l
...              | false = filter p l

length-filter : ∀ {A} (n : ℕ) (l : List A)
                (p₁ : length l ≤ n)
                (p₂ : A → Bool) → (length (filter p₂ l) ≤ n)
length-filter n       []      p₁       p₂ = z≤n
length-filter 0       (_ ∷ _) ()       p₂
length-filter (suc n) (x ∷ l) (s≤s p₁) p₂ with p₂ x
...                                       | true  = s≤s (length-filter n l p₁ p₂)
...                                       | false = ≤-step (length-filter n l p₁ p₂)

qsort₁ : (n : ℕ) (l : List ℕ) → (length l ≤ n) → List ℕ
qsort₁ n       []       p      = []
qsort₁ 0       (_ ∷ _)  ()
qsort₁ (suc n) (x ∷ l) (s≤s p) =
  qsort₁ n (filter (lesseq₁ x) l) (length-filter n l p (lesseq₁ x)) ++
  [ x ] ++
  qsort₁ n (filter (greater₁ x) l) (length-filter n l p (greater₁ x))

≤-refl : ∀ {n} → n ≤ n
≤-refl {0}     = z≤n
≤-refl {suc n} = s≤s (≤-refl)

qsort : List ℕ → List ℕ
qsort l = qsort₁ (length l) l ≤-refl

sorted : List ℕ → Set
sorted []      = ⊤
sorted (x ∷ l) with l
...            | y ∷ m = (x ≤ y) × sorted l
...            | []    = ⊤

occs : ℕ → List ℕ → ℕ
occs _ []      = 0
occs n (m ∷ l) with eq n m
...            | true  = 1 + occs n l
...            | false = occs n l

mem : {A : Set} → A → List A → Set
mem _ []      = ⊥
mem n (m ∷ l) = (n ≡ m) ⊎ mem n l

perm : List ℕ → List ℕ → Set
perm l₁ l₂ = ∀ (n : ℕ) → occs n l₁ ≡ occs n l₂

≤-suc : ∀ {n m} → suc n ≤ m → n ≤ m
≤-suc {n}     {zero}  ()
≤-suc {zero}  {m}     _       = z≤n
≤-suc {suc n} {suc m} (s≤s p) = s≤s (≤-suc p)

sorted₁ : (l m : List ℕ) (a : ℕ) →
          sorted l → sorted m →
          ((b : ℕ) → mem b l → b ≤ a) →
          ((b : ℕ) → mem b m → b > a) →
          sorted (l ++ [ a ] ++ m)
sorted₁ []      []      a sl         sm a≥l m>a = _
sorted₁ []      (n ∷ m) a sl         sm a≥l m>a = ≤-suc (m>a n (inj₁ refl)) , sm
sorted₁ (n ∷ l) m       a sl         sm a≥l m>a with l
sorted₁ (n ∷ l) m       a (n≤b , sl) sm a≥l m>a | (b ∷ l') =
  n≤b , sorted₁ (b ∷ l') m a sl sm (λ x → a≥l x ∘ inj₂) m>a
sorted₁ (n ∷ l) m       a ⊤          sm a≥l m>a | []       =
  a≥l n (inj₁ refl) , sorted₁ [] m a _ sm (λ _ → ⊥-elim) m>a

lesseq-≤ : (x y : ℕ) → (x lesseq y ≡ true) → x ≤ y
lesseq-≤ zero    y       refl = z≤n
lesseq-≤ (suc x) zero    ()
lesseq-≤ (suc x) (suc y) p    = s≤s (lesseq-≤ x y p)

greater-> : (x y : ℕ) → (x greater y ≡ true) → x > y
greater-> zero    y       ()
greater-> (suc x) zero    refl = s≤s z≤n
greater-> (suc x) (suc y) p    = s≤s (greater-> x y p)

lesseq-⊎-greater : (x y : ℕ) → (x lesseq y ≡ true ⊎ x greater y ≡ true)
lesseq-⊎-greater zero    y       = inj₁ refl
lesseq-⊎-greater (suc x) zero    = inj₂ refl
lesseq-⊎-greater (suc x) (suc y) = lesseq-⊎-greater x y

¬-lesseq-×-greater : (x y : ℕ) → ¬ (x lesseq y ≡ true × x greater y ≡ true)
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

mem-filter-greater : (l : List ℕ) (a x : ℕ) →
                    mem x (filter (greater₁ a) l) → x > a
mem-filter-greater l a x p = greater-> x a (mem-filter (greater₁ a) l x p)

≡-pred : ∀ {n m} → suc n ≡ suc m → n ≡ m
≡-pred refl = refl

¬eq-≢ : ∀ {n m} → (eq n m) ≡ false → n ≢ m
¬eq-≢ {zero}  {zero}  () _
¬eq-≢ {zero}  {suc n} p  ()
¬eq-≢ {suc n} {zero}  p  ()
¬eq-≢ {suc n} {suc m} p₁ p₂ with eq n m | inspect (eq n) m
¬eq-≢ {suc n} {suc m} () p₂ | true  | _
¬eq-≢ {suc n} {suc m} p₁ p₂ | false | [ eq ]≡ = (¬eq-≢ eq) (≡-pred p₂)

eq-≡ : ∀ {n m b} → eq n m ≡ b → if b then n ≡ m else n ≢ m
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
...                | true  | [ eq ]≡ = const (s≤s z≤n) , const (inj₁ (eq-≡ eq))
...                | false | [ eq ]≡ =
  (λ { (inj₁ eq₁)   → ⊥-elim (eq-≡ eq eq₁)
     ; (inj₂ memnl) → Prod.proj₁ (mem-occs n l) memnl}) ,
  λ occs>0 → inj₂ (Prod.proj₂ (mem-occs n l) occs>0)

perm-mem : (l₁ l₂ : List ℕ) → perm l₁ l₂ → (x : ℕ) → (mem x l₁ ⇔ mem x l₂)
perm-mem l₁ l₂ p x with mem-occs x l₁ | mem-occs x l₂
perm-mem l₁ l₂ p x | (m₁ , occ₁) | (m₂ , occ₂) =
  (λ m → occ₂ (subst (flip _>_ 0) (p x) (m₁ m))) ,
  (λ m → occ₁ (subst (flip _>_ 0) (sym (p x)) (m₂ m)))

occs-++ : (a : ℕ) (l m : List ℕ) → (occs a (l ++ m) ≡ occs a l + occs a m)
occs-++ a []      m = refl
occs-++ a (x ∷ l) m with occs-++ a l m | eq a x
...                 | occ≡ | true  = cong suc occ≡
...                 | occ≡ | false = occ≡

perm-refl : {l : List ℕ} → perm l l
perm-refl n = refl

perm-sym : {n m : List ℕ} → perm n m → perm m n
perm-sym p x = sym (p x)

perm-trans : {l n m : List ℕ} → perm l n → perm n m → perm l m
perm-trans p₁ p₂ n = trans (p₁ n) (p₂ n)

perm-equivalence : IsEquivalence perm
perm-equivalence = record
  { refl  = perm-refl
  ; sym   = perm-sym
  ; trans = perm-trans
  }

perm-[] : (l : List ℕ) → perm [] l → l ≡ []
perm-[] []      p = refl
perm-[] (x ∷ l) p with p x
perm-[] (x ∷ l) p | occs≡0 with eq x x | ≡→eq x x refl
perm-[] (x ∷ l) p | () | ._ | refl

perm-++₁ : (x l m : List ℕ) (a : ℕ) → perm x (l ++ m) →
           perm (a ∷ x) (l ++ [ a ] ++ m)
perm-++₁ x []      m a p n with eq n a
...                        | true  = cong suc (p n)
...                        | false = p n
perm-++₁ x (y ∷ l) m a p n with eq n y | inspect (eq n) y
perm-++₁ x (y ∷ l) m a p n | true  | [ eq ]≡ = {! !}
perm-++₁ x (y ∷ l) m a p n | false | [ eq ]≡ = {! !}

perm-++₂ : (l₁ l₂ m₁ m₂ : List ℕ) → perm l₁ l₂ → perm m₁ m₂ →
           perm (l₁ ++ m₁) (l₂ ++ m₂)
perm-++₂ []       l₂  m₁ m₂ pl pm n with perm-[] l₂ pl
perm-++₂ []       .[] m₁ m₂ pl pm n | refl = pm n
perm-++₂ (x ∷ l₁) l₂  m₁ m₂ pl pm n = {! !}

perm-filter : (l : List ℕ) (a : ℕ) →
              perm l (filter (lesseq₁ a) l ++ filter (greater₁ a) l)
perm-filter []      a = const refl
perm-filter (x ∷ l) a with perm-filter l a | x lesseq a
perm-filter (x ∷ l) a | p | true  =
  perm-++₁ l [] (filter (lesseq₁ a) l ++ filter (greater₁ a) l) x p
perm-filter (x ∷ l) a | p | false =
  perm-++₁ l (filter (lesseq₁ a) l) (filter (greater₁ a) l) x p

qsort₁-correct : (m : ℕ) (l : List ℕ) (p : length l ≤ m) →
                 (sorted (qsort₁ m l p) × perm l (qsort₁ m l p))
qsort₁-correct 0       []      p       = _ , λ _ → refl
qsort₁-correct 0       (_ ∷ _) ()
qsort₁-correct (suc m) []      p       = _ , λ _ → refl
qsort₁-correct (suc m) (a ∷ l) (s≤s p) =
  let fil₁  = filter (lesseq₁ a) l
      fil₂  = filter (greater₁ a) l
      p₁    = length-filter m l p (lesseq₁ a)
      p₂    = length-filter m l p (greater₁ a)
      l₁    = qsort₁ m fil₁ p₁
      l₂    = qsort₁ m fil₂ p₂
      slpl₁ = qsort₁-correct m fil₁ p₁
      sl₁   = Prod.proj₁ slpl₁
      pl₁   = Prod.proj₂ slpl₁
      slpl₂ = qsort₁-correct m fil₂ p₂
      sl₂   = Prod.proj₁ slpl₂
      pl₂   = Prod.proj₂ slpl₂
      ≤fil  = mem-filter-lesseq l a
      >fil  = mem-filter-greater l a
      pm₁   = perm-mem fil₁ l₁ pl₁
      pm₂   = perm-mem fil₂ l₂ pl₂
      sort  = sorted₁ l₁ l₂ a sl₁ sl₂
                      (λ n m → ≤fil n (Prod.proj₂ (pm₁ n) m))
                      (λ n m → >fil n (Prod.proj₂ (pm₂ n) m))
  in sort , perm-++₁ l l₁ l₂ a
                     (perm-trans {l} {fil₁ ++ fil₂} {l₁ ++ l₂} (perm-filter l a)
                                 (perm-++₂ fil₁ l₁ fil₂ l₂ pl₁ pl₂))

qsort-correct : (l : List ℕ) → (sorted (qsort l) × perm l (qsort l))
qsort-correct = {! !}
