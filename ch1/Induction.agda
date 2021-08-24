module ch1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import ch1.Naturals using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; Bin; _O; _I; ⟨⟩; inc; to; from)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero + zero
  ∎
+-identityʳ (suc m) =
  begin
    (suc m) + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero    n p                          =  refl
+-assoc' (suc m) n p  rewrite +-assoc' m n p  =  refl

+-identityʳ' : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ' zero = refl
+-identityʳ' (suc m) rewrite +-identityʳ' m = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identityʳ m = refl
+-comm' m (suc n)
  rewrite +-suc m n |
          +-comm m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p
  rewrite sym (+-assoc m n p) |
          +-comm m n |
          +-assoc n m p = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p |
          sym (+-assoc p (m * p) (n * p)) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite *-distrib-+ n (m * n) p |
          sym (*-assoc m n p) = refl

*-zeroʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc m) rewrite *-zeroʳ m = refl

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n
  rewrite *-suc m n |
          +-swap n m (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-zeroʳ m = refl
*-comm m (suc n)
  rewrite *-suc m n |
          *-comm m n = refl

∸-zero : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-zero zero = refl
∸-zero (suc n) = refl

∸-+assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+assoc m zero p = refl
∸-+assoc zero (suc n) p rewrite ∸-zero p = refl
∸-+assoc (suc m) (suc n) p rewrite ∸-+assoc m n p = refl

^-distribˡ-+* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-+* m (suc n) p
  rewrite ^-distribˡ-+* m n p |
          sym(*-assoc m (m ^ n) (m ^ p)) = refl

*-swap : ∀ (m n p : ℕ) → m * (n * p) ≡ n * (m * p)
*-swap m n p
  rewrite sym (*-assoc m n p) |
          *-comm m n |
          *-assoc n m p = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite ^-distribʳ-* m n p |
          *-assoc m n ((m ^ p) * (n ^ p)) |
          *-swap n (m ^ p) (n ^ p) |
          sym (*-assoc m (m ^ p) (n * (n ^ p))) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-zeroʳ n = refl
^-*-assoc m n (suc p)
  rewrite ^-*-assoc m n p |
          sym (^-distribˡ-+* m n (n * p)) |
          sym (*-suc n p) = refl

-- to (from n) ≢ n
-- Counterexample:
-- begin
--   to (from ⟨⟩)
-- ≡⟨⟩
--   to zero
-- ≡⟨⟩
--   ⟨⟩
-- ∎

from-inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc ⟨⟩ = refl
from-inc (b O)
  rewrite +-assoc (from b) (from b + 0) 1 |
          +-comm (from b + 0) 1 |
          +-suc (from b) (from b + 0) = refl
from-inc (b I)
  rewrite from-inc b |
          +-comm 1 (from b + 0) |
          +-assoc (from b) 0 1 |
          sym (+-assoc (from b) (from b) 1) |
          +-comm (from b) 0 = refl

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n)
  rewrite from-inc (to n) |
          from-to n = refl
