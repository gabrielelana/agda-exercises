module EvenOrOdd where

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
  zero : Even 0
  step : {n : ℕ} → Even n → Even (suc (suc n))

-- Define Odd numbers constructively
data Odd : ℕ → Set where
  one : Odd 1
  step : {n : ℕ} → Odd n → Odd (suc (suc n))

-- Prove: every number is either even or odd
evenOrOdd : ∀ (n : ℕ) → Even n ⊎ Odd n
evenOrOdd zero = inj₁ zero
evenOrOdd (suc zero) = inj₂ one
evenOrOdd (suc (suc n)) with evenOrOdd n
... | inj₁ even = inj₁ (step even)
... | inj₂ odd = inj₂ (step odd)

-- Prove: no number is both even and odd
evenOddDisjoint : ∀ (n : ℕ) → Even n → Odd n → ⊥
evenOddDisjoint zero _ ()
evenOddDisjoint (suc zero) ()
evenOddDisjoint (suc (suc n)) (step even-n) (step odd-n) = evenOddDisjoint n even-n odd-n

-- Prove: Even is decidable
decEven : ∀ (n : ℕ) → Dec (Even n)
decEven zero = yes zero
decEven (suc zero) = no λ ()
decEven (suc (suc n)) with decEven n
... | yes p = yes (step p)
... | no ¬p = no λ { (step p) → ¬p p }

-- Prove: Odd is decidable
decOdd : ∀ (n : ℕ) → Dec (Odd n)
decOdd zero = no λ ()
decOdd (suc zero) = yes one
decOdd (suc (suc n)) with decOdd n
... | yes p = yes (step p)
... | no ¬p = no λ { (step p) → ¬p p }

-- Prove that every even number is multiple of 2
evenIsPairMultiple : ∀ (n : ℕ) → Even n → ∃ λ k → n ≡ k * 2
evenIsPairMultiple zero zero = zero , refl
evenIsPairMultiple (suc (suc n)) (step even) with evenIsPairMultiple n even
... | k , p = suc k , cong (suc ∘ suc) p

-- Prove that `suc` flips parity
sucFlipsParityEvenToOdd : ∀ (n : ℕ) → Even n → Odd (suc n)
sucFlipsParityEvenToOdd zero _ = one
sucFlipsParityEvenToOdd (suc (suc n)) (step even) = step (sucFlipsParityEvenToOdd n even)

sucFlipsParityOddToEven : ∀ (n : ℕ) → Odd n → Even (suc n)
sucFlipsParityOddToEven (suc zero) _ = step zero
sucFlipsParityOddToEven (suc (suc n)) (step odd) = step (sucFlipsParityOddToEven n odd)

-- Proves related to sum
evenPlusEvenIsEven : ∀ {m n} → Even m → Even n → Even (m + n)
evenPlusEvenIsEven zero q = q
evenPlusEvenIsEven (step p) q = step (evenPlusEvenIsEven p q)

oddPlusOddIsEven : ∀ {m n} → Odd m → Odd n → Even (m + n)
oddPlusOddIsEven one one = step zero
oddPlusOddIsEven one (step q) = oddPlusOddIsEven (step one) q
oddPlusOddIsEven (step p) q = step (oddPlusOddIsEven p q)
