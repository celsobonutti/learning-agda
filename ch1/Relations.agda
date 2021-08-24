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
