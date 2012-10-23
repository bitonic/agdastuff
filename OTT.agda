module OTT where

open import Data.Nat

data Empty : Set where

⊥-elim : {A : Set} → Empty -> A
⊥-elim ()

record Unit : Set where

data Bool : Set where
  tt : Bool
  ff : Bool

record Σ (S : Set) (T : S → Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst

data W (S : Set) (T : S → Set) : Set where
  _◃_ : (x : S) → (T x → W S T) → W S T

mutual
  data ‘set’ : Set where
    ‘0’ : ‘set’
    ‘1’ : ‘set’
    ‘2’ : ‘set’
    ‘Π’ : (S : ‘set’) → (〚 S 〛 → ‘set’) → ‘set’
    ‘Σ’ : (S : ‘set’) → (〚 S 〛 → ‘set’) → ‘set’
    ‘W’ : (S : ‘set’) → (〚 S 〛 → ‘set’) → ‘set’

  〚_〛 : ‘set’ → Set
  〚 ‘0’ 〛     = Empty
  〚 ‘1’ 〛     = Unit
  〚 ‘2’ 〛     = Bool
  〚 ‘Π’ S T 〛 = (x : 〚 S 〛) → 〚 T x 〛
  〚 ‘Σ’ S T 〛 = Σ 〚 S 〛 (λ x → 〚 T x 〛)
  〚 ‘W’ S T 〛 = W 〚 S 〛 (λ x → 〚 T x 〛)

mutual
  data ‘prop’ : Set where
    ‘⊥’   : ‘prop’
    ‘⊤’   : ‘prop’
    _‘∧’_ : ‘prop’ → ‘prop’ → ‘prop’
    ‘∀’   : (S : ‘set’) → (〚 S 〛 → ‘prop’) → ‘prop’

  ⌈_⌉ : ‘prop’ → ‘set’
  ⌈ ‘⊥’ ⌉     = ‘0’
  ⌈ ‘⊤’ ⌉     = ‘1’
  ⌈ P ‘∧’ Q ⌉ = ‘Σ’ ⌈ P ⌉ (λ _ → ⌈ Q ⌉)
  ⌈ ‘∀’ S T ⌉ = ‘Π’ S (λ t → ⌈ T t ⌉)

_‘⇒’_ : ‘prop’ → ‘prop’ → ‘prop’
P ‘⇒’ Q = ‘∀’ ⌈ P ⌉ (λ _ → Q)

mutual
  Eq : ‘set’ → ‘set’ → ‘prop’
  Eq ‘0’          ‘0’        = ‘⊤’
  Eq ‘1’          ‘1’        = ‘⊤’
  Eq ‘2’          ‘2’        = ‘⊤’
  Eq (‘Π’ S₀ T₀) (‘Π’ S₁ T₁) = EqBinder S₀ T₀ S₁ T₁
  Eq (‘Σ’ S₀ T₀) (‘Σ’ S₁ T₁) = EqBinder S₁ T₁ S₀ T₀
  Eq (‘W’ S₀ T₀) (‘W’ S₁ T₁) = EqBinder S₀ T₀ S₁ T₁
  Eq  _           _          = ‘⊥’

  EqBinder : (S₀ : ‘set’) → (〚 S₀ 〛 → ‘set’) → (S₁ : ‘set’) → (〚 S₁ 〛 → ‘set’) → ‘prop’
  EqBinder S₀ T₀ S₁ T₁ =
    Eq S₁ S₀ ‘∧’ (‘∀’ S₀ (λ x₀ → ‘∀’ S₁ (λ x₁ → eq S₀ x₀ S₁ x₁ ‘⇒’ Eq (T₀ x₀) (T₁ x₁))))
  
  eq : (S : ‘set’) → 〚 S 〛 → (T : ‘set’) → 〚 T 〛 → ‘prop’
  eq ‘0’ _  ‘0’ _  = ‘⊤’
  eq ‘1’ _  ‘1’ _  = ‘⊤’
  eq ‘2’ tt ‘2’ tt = ‘⊤’
  eq ‘2’ ff ‘2’ ff = ‘⊤’
  eq ‘2’ _  ‘2’ _  = ‘⊥’
  eq _   _ _   _ = {! !}

mutual
  coe : (S : ‘set’) (T : ‘set’) → 〚 ⌈ Eq S T ⌉ 〛 → 〚 S 〛 → 〚 T 〛
  coe ‘0’ ‘0’ Q z = z
  coe _   _   _ _ = {! !}

  coh : (S : ‘set’) (T : ‘set’) (Q : 〚 ⌈ Eq S T ⌉ 〛) (s : 〚 S 〛) → 〚 ⌈ eq S s T (coe S T Q s) ⌉ 〛
  coh S T Q s = {! !}
