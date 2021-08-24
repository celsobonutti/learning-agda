module ch1.Naturals where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m    ∸ zero   = m
zero ∸ n      = zero
suc m ∸ suc n = m ∸ n

_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

infixl 6 _+_ _∸_
infixl 7 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}


-- Exercise `Bin`

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

_ : inc ⟨⟩ ≡ ⟨⟩ I
_ =
  begin
    inc ⟨⟩
  ≡⟨⟩
    ⟨⟩ I
  ∎

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ =
  begin
    inc (⟨⟩ I)
  ≡⟨⟩
    (inc ⟨⟩) O
  ≡⟨⟩
    ⟨⟩ I O
  ∎

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ =
  begin
    inc (⟨⟩ I O)
  ≡⟨⟩
    ⟨⟩ I I
  ∎

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ =
  begin
    inc (⟨⟩ I I)
  ≡⟨⟩
    (inc (⟨⟩ I)) O
  ≡⟨⟩
    ((inc ⟨⟩) O) O
  ≡⟨⟩
    ⟨⟩ I O O
  ∎

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = 2 * from x
from (x I) = 2 * from x + 1
