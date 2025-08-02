module FizzBuzz_Holey where

-- FizzBuzz problem: given a list of natural numbers between 1 and `n`, for
-- every number `i` in the list, print

-- "FizzBuzz" if `i` is divisible by 3 and 5.
-- "Fizz" if `i` is divisible by 3.
-- "Buzz" if `i` is divisible by 5.
-- The number itself as a string, if none of the previous conditions are true.

-- Our goal is not to solve the problem per se, but to try to Agda to come up
-- with a solution which should be correct by construction.

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (Σ; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)

-- Fizzy represents the divisibility by 3 of a natural number
data Fizzy : ℕ → Set where
  Z : Fizzy 0
  S : {n : ℕ} → Fizzy n → Fizzy (3 + n)

-- Prove that is true
fizzyOk : ∀ (n : ℕ) → Fizzy n → Σ ℕ (λ k → n ≡ k * 3)
fizzyOk = {!!}

-- Prove that Fizzy is decidable
decFizzy : (n : ℕ) → Dec (Fizzy n)
decFizzy = {!!}

-- Buzzy represents the divisibility by 5 of a natural number
data Buzzy : ℕ → Set where
  Z : Buzzy 0
  S : {n : ℕ} → Buzzy n → Buzzy (5 + n)

-- Prove that is true
buzzyOk : ∀ (n : ℕ) → Buzzy n → Σ ℕ (λ k → n ≡ k * 5)
buzzyOk = {!!}

-- Prove that Buzzy is decidable
decBuzzy : (n : ℕ) → Dec (Buzzy n)
decBuzzy = {!!}

-- This is going to be used as type to classify every natural number accordingly
-- with the FizzBuzz's rules. NOTE: you can create an instance of `FizzBuzz` for
-- `n` only if you have suitable proofs.
data FizzBuzz : Set where
  None : (n : ℕ) → ¬ Fizzy n → ¬ Buzzy n → FizzBuzz
  Fizz : {n : ℕ} → Fizzy n → ¬ Buzzy n → FizzBuzz
  Buzz : {n : ℕ} → ¬ Fizzy n → Buzzy n → FizzBuzz
  Both : {n : ℕ} → Fizzy n → Buzzy n → FizzBuzz

to : ℕ → FizzBuzz
to = {!!}

toString : FizzBuzz → String
toString = {!!}

fizzBuzzTo : ℕ → List String
fizzBuzzTo = {!!}

-- Acceptance test
_ : fizzBuzzTo 15 ≡ "1" ∷ "2" ∷ "Fizz" ∷ "4" ∷ "Buzz" ∷ "Fizz" ∷ "7" ∷ "8" ∷ "Fizz" ∷ "Buzz" ∷ "11" ∷ "Fizz" ∷ "13" ∷ "14" ∷ "FizzBuzz" ∷ []
_ = {!!}
