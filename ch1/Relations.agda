module ch1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

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
