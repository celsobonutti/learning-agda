module ch1.Bin where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open Eq using (_≡_; _≢_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-comm; +-assoc; +-suc)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = 2 * from x
from (x I) = 2 * from x + 1

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

to-suc : ∀ (n : ℕ) → to (suc n) ≡ inc (to n)
to-suc zero = refl
to-suc (suc n) = refl

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n)
  rewrite from-inc (to n) |
          from-to n = refl
