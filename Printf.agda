-- Ripped off
-- <https://github.com/liamoc/learn-you-an-agda/blob/master/Printf.agda>
module Printf where

open import Data.List hiding(_++_)
open import Data.String
open import Data.Unit
open import Data.Empty
open import Data.Char
open import Data.Product
open import Data.Nat.Show renaming (show to showNat)
open import Data.Nat
open import Function using (_∘_; id)

singleton : Char → String
singleton = fromList ∘ [_]

data Fmt : Set₁ where
   arg : {A : Set} → (A → String) → Fmt
   lit  : Char → Fmt

data Parse : Set₁ where
   valid   : List Fmt → Parse
   invalid : Parse

parse : String → Parse
parse s = parse′ [] (toList s)
  where
    parse′ : List Fmt → List Char → Parse
    parse′ l ('%' ∷ 's' ∷ fmt) = parse′ (arg id ∷ l) fmt
    parse′ l ('%' ∷ 'c' ∷ fmt) = parse′ (arg singleton ∷ l) fmt
    parse′ l ('%' ∷ 'd' ∷ fmt) = parse′ (arg showNat ∷ l) fmt
    parse′ l ('%' ∷ '%' ∷ fmt) = parse′ (lit '%' ∷ l) fmt
    parse′ l ('%' ∷ c ∷ fmt) = invalid
    parse′ l (c ∷ fmt) = parse′ (lit c ∷ l) fmt
    parse′ l [] = valid (reverse l)

Args : Parse → Set
Args invalid = ⊥ → String
Args (valid (arg {t} _ ∷ r)) = t → (Args (valid r))
Args (valid (lit _ ∷ r)) = Args (valid r)
Args (valid []) = String

sprintf : (f : String) → Args (parse f)
sprintf = sprintf′ "" ∘ parse
  where
    sprintf′ : String → (f : Parse) → Args f
    sprintf′ acc invalid = λ t → ""
    sprintf′ acc (valid []) = acc
    sprintf′ acc (valid (arg s ∷ l)) = λ t → (sprintf′ (acc ++ s t) (valid l))
    sprintf′ acc (valid (lit c ∷ l)) = sprintf′ (acc ++ singleton c) (valid l)
