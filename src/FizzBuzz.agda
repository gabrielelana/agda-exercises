module FizzBuzz where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Product using (Σ; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.String using (String)
open import Data.Nat.Show using (show)
open import Data.List using (List; []; _∷_; upTo; map)
open import Data.Bool.Base using (Bool; true; false)

data DivisibleBy (k : ℕ) : ℕ → Set where
  zero : DivisibleBy k 0
  step : {n : ℕ} → DivisibleBy k n → DivisibleBy k (k + n)

-- Can build `Fizzy n` only if `n` is multiple of 3
Fizzy = DivisibleBy 3

-- `Fizzy 0` exists
_ : Fizzy 0
_ = zero

-- `Fizzy 1` doesn't exists
_ : Fizzy 1 → ⊥
_ = λ ()

-- `Fizzy 3` exists
_ : Fizzy 3
_ = step zero

-- Prove that for every `n : ℕ` if it exists a `Fizzy n` then exists a `k : ℕ`
-- such that `n ≡ k * 3` (which is to say that n is multiple of 3)
fizzyOk : ∀ (n : ℕ) → Fizzy n → Σ ℕ (λ k → n ≡ k * 3)
fizzyOk zero x = zero , refl
fizzyOk (suc (suc (suc n))) (step z) with fizzyOk n z
... | k , p = suc k , cong (suc ∘ suc ∘ suc) p

-- Prove that Fizzy is decidable: for any `n : ℕ`, either construct a proof that
-- n is divisible by 3 (with proof `p : Fizzy n`), or prove that it's not
-- divisible by 3 (with proof `¬p : ¬ Fizzy n`)
decFizzy : (n : ℕ) → Dec (Fizzy n)
decFizzy zero = yes zero
decFizzy (suc zero) = no λ ()
decFizzy (suc (suc zero)) = no λ ()
decFizzy (suc (suc (suc k))) with (decFizzy k)
... | yes p = yes (step p)
... | no ¬p = no λ {(step p) → ¬p p }

-- Can build `Buzzy n` only if `n` is multiple of 5
Buzzy = DivisibleBy 5

-- Prove that for every `n : ℕ` if it exists a `Buzzy n` then exists a `k : ℕ`
-- such that `n ≡ k * 5` (which is to say that n is multiple of 5)
buzzyOk : ∀ (n : ℕ) → Buzzy n → Σ ℕ (λ k → n ≡ k * 5)
buzzyOk zero x = zero , refl
buzzyOk (suc (suc (suc (suc (suc n))))) (step z) with buzzyOk n z
... | k , p = suc k , cong (suc ∘ suc ∘ suc ∘ suc ∘ suc) p

-- Prove that Buzzy is decidable: for any `n : ℕ`, either construct a proof that
-- n is divisible by 5 (with proof `p : Buzzy n`), or prove that it's not
-- divisible by 5 (with proof `¬p : ¬ Buzzy n`)
decBuzzy : (n : ℕ) → Dec (Buzzy n)
decBuzzy zero = yes zero
decBuzzy (suc zero) = no λ ()
decBuzzy (suc (suc zero)) = no λ ()
decBuzzy (suc (suc (suc zero))) = no λ ()
decBuzzy (suc (suc (suc (suc zero)))) = no λ ()
decBuzzy (suc (suc (suc (suc (suc k))))) with (decBuzzy k)
... | yes p = yes (step p)
... | no ¬p = no λ {(step p) → ¬p p }

data FizzBuzz : Set where
  None : (n : ℕ) → ¬ Fizzy n → ¬ Buzzy n → FizzBuzz
  Fizz : {n : ℕ} → Fizzy n → ¬ Buzzy n → FizzBuzz
  Buzz : {n : ℕ} → ¬ Fizzy n → Buzzy n → FizzBuzz
  Both : {n : ℕ} → Fizzy n → Buzzy n → FizzBuzz

-- Convert a natural number in `FizzBuzz` which can be built only if we have
-- proof of the divisibility of `n` (i.e. its fizzyness or buzzyness)
to : ℕ → FizzBuzz
to n  with decFizzy n | decBuzzy n
... | yes df | yes db = Both df db
... | yes df | no ¬db = Fizz df ¬db
... | no ¬df | yes db = Buzz ¬df db
... | no ¬df | no ¬db = None n ¬df ¬db

_ : ∃[ ¬fizz ] ∃[ ¬buzz ] (to 1 ≡ None 1 ¬fizz ¬buzz)
_ = _ , _ , refl

_ : ∃[ fizz ] ∃[ ¬buzz ] (to 3 ≡ Fizz fizz ¬buzz)
_ = _ , _ , refl

_ : ∃[ ¬fizz ] ∃[ buzz ] (to 5 ≡ Buzz ¬fizz buzz)
_ = _ , _ , refl

_ : ∃[ fizz ] ∃[ buzz ] (to 15 ≡ Both fizz buzz)
_ = _ , _ , refl

-- Convert an instance of FizzBuzz to a string to show the user the result of
-- the computation
toString : FizzBuzz → String
toString (None x _ _) = show x
toString (Fizz _ _) = "Fizz"
toString (Buzz _ _) = "Buzz"
toString (Both _ _) = "FizzBuzz"

-- Final utility function to generate a list of strings to show to the user
fizzBuzzTo : ℕ → List String
fizzBuzzTo n = map (toString ∘ to ∘ suc) (upTo n)

_ : fizzBuzzTo 15 ≡ "1" ∷ "2" ∷ "Fizz" ∷ "4" ∷ "Buzz" ∷ "Fizz" ∷ "7" ∷ "8" ∷ "Fizz" ∷ "Buzz" ∷ "11" ∷ "Fizz" ∷ "13" ∷ "14" ∷ "FizzBuzz" ∷ []
_ = refl
