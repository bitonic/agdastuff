module TypeIneq where

open import Function
open import Data.Nat
open import Data.Bool
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
import Level

ℕ≢Bool : ℕ ≢ Bool
ℕ≢Bool p = boom
  where
    record IsNat (X : Set) : Set where
      field
        to      : ℕ → X
        from    : X → ℕ
        from-to : ∀ {x} → from (to x) ≡ x

    ℕ↔Bool : IsNat Bool
    ℕ↔Bool = subst IsNat p record {to = id; from = id; from-to = refl}
    open IsNat ℕ↔Bool

    to≡ : ∀ {x y} → to x ≡ to y → x ≡ y
    to≡ p = subst₂ _≡_ from-to from-to (cong from p)

    ≢ℕ : ∀ x y → x ≢ y → to x ≢ to y
    ≢ℕ x y x≢y = x≢y ∘ to≡

    ≡Bool : to 0 ≡ to 1 ⊎ to 1 ≡ to 2 ⊎ to 0 ≡ to 2
    ≡Bool with to 0 | to 1 | to 2
    ≡Bool | _     | true  | true  = inj₂ (inj₁ refl)
    ≡Bool | _     | false | false = inj₂ (inj₁ refl)
    ≡Bool | true  | _     | true  = inj₂ (inj₂ refl)
    ≡Bool | false | _     | false = inj₂ (inj₂ refl)
    ≡Bool | true  | true  | _     = inj₁ refl
    ≡Bool | false | false | _     = inj₁ refl

    boom : ⊥
    boom with ≡Bool
    boom | inj₁ to0≡to1        = ≢ℕ 0 1 (λ()) to0≡to1
    boom | inj₂ (inj₁ to1≡to2) = ≢ℕ 1 2 (λ()) to1≡to2
    boom | inj₂ (inj₂ to0≡to2) = ≢ℕ 0 2 (λ()) to0≡to2

shachaf : (∀ {ℓ} (P : Set → Set ℓ) → P ℕ → P Bool) → ⊥
shachaf f = ℕ≢Bool (f (λ X → ℕ ≡ X) refl)
