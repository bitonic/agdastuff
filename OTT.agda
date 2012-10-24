module OTT where

open import Data.Nat

data Empty : Set where

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
  Eq (‘Π’ S₀ T₀) (‘Π’ S₁ T₁) =
    Eq S₁ S₀ ‘∧’ (‘∀’ S₁ (λ x₁ → ‘∀’ S₀ (λ x₀ → eq S₁ x₁ S₀ x₀ ‘⇒’ Eq (T₀ x₀) (T₁ x₁))))
  Eq (‘Σ’ S₀ T₀) (‘Σ’ S₁ T₁) =
    Eq S₀ S₁ ‘∧’ (‘∀’ S₀ (λ x₀ → ‘∀’ S₁ (λ x₁ → eq S₀ x₀ S₁ x₁ ‘⇒’ Eq (T₀ x₀) (T₁ x₁))))
  Eq (‘W’ S₀ T₀) (‘W’ S₁ T₁) =
    Eq S₀ S₁ ‘∧’ (‘∀’ S₀ (λ x₀ → ‘∀’ S₁ (λ x₁ → eq S₀ x₀ S₁ x₁ ‘⇒’ Eq (T₁ x₁) (T₀ x₀))))
  Eq  _           _          = ‘⊥’

  eq : (S : ‘set’) → 〚 S 〛 → (T : ‘set’) → 〚 T 〛 → ‘prop’
  eq  ‘0’         _         ‘0’         _        = ‘⊤’
  eq  ‘1’         _         ‘1’         _        = ‘⊤’
  eq  ‘2’         tt        ‘2’         tt       = ‘⊤’
  eq  ‘2’         ff        ‘2’         ff       = ‘⊤’
  eq (‘Π’ S₀ T₀)  f₀       (‘Π’ S₁ T₁)  f₁       = {! !}
  eq (‘Σ’ S₀ T₀) (s₀ , t₀) (‘Σ’ S₁ T₁) (s₁ , t₁) = {! !}
  eq (‘W’ S₀ T₀) (s₀ ◃ f₀) (‘W’ S₁ T₁) (s₁ ◃ f₁) = {! !}
  eq  _           _         _           _        = ‘⊥’

mutual
  coe : (S : ‘set’) (T : ‘set’) → 〚 ⌈ Eq S T ⌉ 〛 → 〚 S 〛 → 〚 T 〛
  coe ‘0’          ‘0’         _         z        = z
  coe ‘1’          ‘1’         _         u        = u
  coe ‘2’          ‘2’         _         b        = b
  coe (‘Π’ S₀ T₀) (‘Π’ S₁ T₁) Q          f₀       = coeΠ S₀ T₀ S₁ T₁ Q f₀
  coe (‘Σ’ S₀ T₀) (‘Σ’ S₁ T₁) (Qs , Qt) (s₀ , t₀) with coe S₀ S₁ Qs s₀ | coh S₀ S₁ Qs s₀
  ... | s₁ | foo = s₁ , coe (T₀ s₀) (T₁ s₁) (Qt s₀ s₁ foo) t₀
  coe (‘W’ S₀ T₀) (‘W’ S₁ T₁) (Qs , Qt) (s₀ ◃ f₀) with coe S₀ S₁ Qs s₀ | coh S₀ S₁ Qs s₀
  ... | s₁ | foo = s₁ ◃ (λ t₁ → coe (‘W’ S₀ T₀) (‘W’ S₁ T₁) (Qs , Qt)
                                    (f₀ (coe (T₁ s₁) (T₀ s₀) (Qt s₀ s₁ foo) t₁)))
  coe ‘0’           ‘1’        ()        _
  coe ‘0’           ‘2’        ()        _
  coe ‘0’          (‘Π’ _ _)   ()        _
  coe ‘0’          (‘Σ’ _ _)   ()        _
  coe ‘0’          (‘W’ _ _)   ()        _
  coe ‘1’           ‘0’        ()        _
  coe ‘1’           ‘2’        ()        _
  coe ‘1’          (‘Π’ _ _)   ()        _
  coe ‘1’          (‘Σ’ _ _)   ()        _
  coe ‘1’          (‘W’ _ _)   ()        _
  coe ‘2’           ‘0’        ()        _
  coe ‘2’           ‘1’        ()        _
  coe ‘2’          (‘Π’ _ _)   ()        _
  coe ‘2’          (‘Σ’ _ _)   ()        _
  coe ‘2’          (‘W’ _ _)   ()        _
  coe (‘Π’ _ _)     ‘0’        ()        _
  coe (‘Π’ _ _)     ‘1’        ()        _
  coe (‘Π’ _ _)     ‘2’        ()        _
  coe (‘Π’ _ _)    (‘Σ’ _ _)   ()        _
  coe (‘Π’ _ _)    (‘W’ _ _)   ()        _
  coe (‘Σ’ _ _)     ‘0’        ()        _
  coe (‘Σ’ _ _)     ‘1’        ()        _
  coe (‘Σ’ _ _)     ‘2’        ()        _
  coe (‘Σ’ _ _)    (‘Π’ _ _)   ()        _
  coe (‘Σ’ _ _)    (‘W’ _ _)   ()        _
  coe (‘W’ _ _)     ‘0’        ()        _
  coe (‘W’ _ _)     ‘1’        ()        _
  coe (‘W’ _ _)     ‘2’        ()        _
  coe (‘W’ _ _)    (‘Π’ _ _)   ()        _
  coe (‘W’ _ _)    (‘Σ’ _ _)   ()        _

  coeΠ : (S₀ : ‘set’) (T₀ : 〚 S₀ 〛 → ‘set’) (S₁ : ‘set’) (T₁ : 〚 S₁ 〛 → ‘set’) →
         〚 ⌈ Eq (‘Π’ S₀ T₀) (‘Π’ S₁ T₁) ⌉ 〛 → 〚 ‘Π’ S₀ T₀ 〛 →
         (x : 〚 S₁ 〛) → 〚 T₁ x 〛
  coeΠ S₀ T₀ S₁ T₁ (Qs , Qt) f₀ s₁ with coe S₁ S₀ Qs s₁ | coh S₁ S₀ Qs s₁
  ... | s₀ | foo = coe (T₀ s₀) (T₁ s₁) (Qt s₁ s₀ foo) (f₀ s₀)

  coh : (S : ‘set’) (T : ‘set’) (Q : 〚 ⌈ Eq S T ⌉ 〛) (s : 〚 S 〛) →
        〚 ⌈ eq S s T (coe S T Q s) ⌉ 〛
  coh S T Q s = {! !}
