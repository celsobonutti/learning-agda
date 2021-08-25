module ch1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
      ----------
      → zero ≤ n

  s≤s : ∀ {m n : ℕ} → m ≤ n
      ---------------
      → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
        → suc m ≤ suc n
        -------
        → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

-- Preorder example
-- f(a) ≤ f(b) where f(x) = x²
-- i.e. f(2) ≤ f(-2) and f(-2) ≤ f(2) => 4 ≤ 4, but 2 ≢ -2

-- Partial order example
-- Consider the set of subsets of {0, 1}:
-- And its subsets ∅, {0}, {1} and {0, 1}.
-- The `subset` relation between these sets is:
-- 1. Reflexive: for all sets S, S ⊂ S
-- 2. Transitive: if S₁ ⊂ S₂ and S₂ ⊂ S₃, then S₁ ⊂ S₃:
--   - ∅ ⊂ {0} and {0} ⊂ {0, 1}, so ∅ ⊂ {0, 1}
-- 3. Anti-symmetric: if S₁ ⊂ S₂ and S₂ ⊂ S₁, then S₁ ≡ S₂
--   - If every element of S₁ is inside S₂ and every elemento of S₂ is inside S₁
--     then, S₁ must be equal to S₂
-- But it is not Total:
-- {1} ⊄ {0}, and {0} ⊄ {1}.

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n

  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

≤-total' : ∀ (m n : ℕ) → Total m n
≤-total' zero n = forward z≤n
≤-total' (suc m) zero = flipped z≤n
≤-total' (suc m) (suc n) = helper (≤-total' m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n) = forward (s≤s m≤n)
  helper (flipped n≤m) = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n
  rewrite +-comm m p |
          +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans m+p≤n+p n+p≤n+q
  where
    m+p≤n+p : m + p ≤ n + p
    m+p≤n+p = +-monoˡ-≤ m n p m≤n

    n+p≤n+q : n + p ≤ n + q
    n+p≤n+q = +-monoʳ-≤ n p q p≤q

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q n*p≤n*q
  where
    n*p≤n*q : n * p ≤ n * q
    n*p≤n*q = *-monoʳ-≤ n p q p≤q

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n
  rewrite *-comm m p |
          *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans m*p≤n*p n*p≤n*q
  where
    m*p≤n*p : m * p ≤ n * p
    m*p≤n*p = *-monoˡ-≤ m n p m≤n
    n*p≤n*q : n * p ≤ n * q
    n*p≤n*q = *-monoʳ-≤ n p q p≤q

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n

  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

inv-s<s : {m n : ℕ} → suc m < suc n → m < n
inv-s<s (s<s sm<sn) = sm<sn

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

≤-iff-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-iff-< {zero} {suc n} _ = z<s
≤-iff-< {suc m} {suc n} (s≤s sm≤n) = s<s (≤-iff-< {m} {n} sm≤n)

<-iff-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-iff-≤ {zero} {suc n} _ = s≤s z≤n
<-iff-≤ {suc m} {suc n} m<n = s≤s (<-iff-≤ {m} {n} (inv-s<s m<n))

data _>_ : ℕ → ℕ → Set where
  inv-< : ∀ {m n : ℕ} → n < m → m > n

data Trichotomy (m n : ℕ) : Set where
  smaller : m < n → Trichotomy m n
  equal : m ≡ n → Trichotomy m n
  bigger : m > n → Trichotomy m n

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = equal refl
trichotomy zero (suc n) = smaller z<s
trichotomy (suc m) zero = bigger (inv-< (z<s))
trichotomy (suc m) (suc n) with trichotomy m n
...                           | smaller m<n = smaller (s<s m<n)
...                           | equal refl  = equal refl
...                           | bigger (inv-< n<m) = bigger (inv-< (s<s n<m))

+-monoʳ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n
  rewrite +-comm m p |
          +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

<-suc : ∀ (n : ℕ) → n < suc n
<-suc zero = z<s
<-suc (suc n) = s<s (<-suc n)

-- <-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
-- <-trans-revisited z<s (s<s n<p) = z<s
-- <-trans-revisited (s<s m<n) (s<s n<p) = {!sm<n!}
--   where
--     ssm≤sn = s≤s (<-iff-≤ m<n)
--     sn≤p = <-iff-≤ n<p
--     sm<n = ≤-iff-< (≤-trans ssm≤sn sn≤p)
