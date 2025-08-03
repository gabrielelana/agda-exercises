module EvenOrOdd_Holey where

-- In this exercise, you'll create a type-safe, mathematically rigorous
-- implementation of even and odd numbers in Agda. Unlike traditional
-- programming where you might just use n % 2 == 0, we'll encode the
-- mathematical properties directly into the type system.
--
-- This exercise teaches core Agda concepts you'll use everywhere:
--
-- Inductive datatypes that encode mathematical properties
-- Constructive proofs where existence means construction
-- Decision procedures that compute proofs
-- Totality and disjointness - fundamental logical properties

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function.Base using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_)
open import Data.Product using (∃)

-- Define Even numbers constructively
data Even : ℕ → Set where

-- Define Odd numbers constructively
data Odd : ℕ → Set where

-- Prove: every number is either even or odd
evenOrOdd : ∀ (n : ℕ) → Even n ⊎ Odd n
evenOrOdd = {!!}

-- Prove: no number is both even and odd
evenOddDisjoint : ∀ (n : ℕ) → Even n → Odd n → ⊥
evenOddDisjoint = {!!}

-- Prove: Even is decidable
decEven : ∀ (n : ℕ) → Dec (Even n)
decEven = {!!}

-- Prove: Odd is decidable
decOdd : ∀ (n : ℕ) → Dec (Odd n)
decOdd = {!!}

-- Prove that every even number is multiple of 2
evenIsPairMultiple : ∀ (n : ℕ) → Even n → ∃ λ k → n ≡ k * 2
evenIsPairMultiple = {!!}

-- Prove that `suc` flips parity
sucFlipsParityEvenToOdd : ∀ (n : ℕ) → Even n → Odd (suc n)
sucFlipsParityEvenToOdd = {!!}

sucFlipsParityOddToEven : ∀ (n : ℕ) → Odd n → Even (suc n)
sucFlipsParityOddToEven = {!!}

-- Proves related to sum
evenPlusEvenIsEven : ∀ {m n} → Even m → Even n → Even (m + n)
evenPlusEvenIsEven = {!!}

oddPlusOddIsEven : ∀ {m n} → Odd m → Odd n → Even (m + n)
oddPlusOddIsEven = {!!}
