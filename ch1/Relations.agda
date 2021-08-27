module ch1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm; +-assoc; +-suc)
open import ch1.Bin using (Bin; inc; to; from; ⟨⟩; _O; _I; from-inc; to-suc)

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

≤-suc-trans : ∀ {n m} → m ≤ n → m ≤ suc n
≤-suc-trans z≤n = z≤n
≤-suc-trans (s≤s m≤n) = s≤s (≤-suc-trans m≤n)

<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited {m} {n} {p} m<n n<p = ≤-iff-< sm≤p
  where
    sm≤n : suc m ≤ n
    sm≤n = <-iff-≤ m<n
    sm≤sn : suc m ≤ suc n
    sm≤sn = ≤-suc-trans sm≤n
    sn≤p : suc n ≤ p
    sn≤p = <-iff-≤ n<p
    sm≤p : suc m ≤ p
    sm≤p = ≤-trans sm≤sn sn≤p

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en  = suc (e+e≡e em en)

+-comm-e : ∀ {m n : ℕ} → even (m + n) → even (n + m)
+-comm-e {m} {n} emn rewrite +-comm m n = emn

+-comm-o : ∀ {m n : ℕ} → odd (m + n) → odd (n + m)
+-comm-o {m} {n} omn rewrite +-comm m n = omn

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e {suc m} {n} (suc em) on = suc omn
  where
    omn : odd (m + n)
    omn = +-comm-o {n} {m} (o+e≡o on em)

rest : Bin → Bin
rest ⟨⟩ = ⟨⟩
rest (r I) = r
rest (r O) = r

data One : Bin -> Set
data One where
  one : One (⟨⟩ I)
  case-O : ∀ {b : Bin} → One b → One (b O)
  case-I : ∀ {b : Bin} → One b → One (b I)

data Can : Bin → Set
data Can where
  zero : Can (⟨⟩ O)
  from-one : ∀ {b : Bin} → One b → Can b

one-inc : ∀ {b : Bin} → One b → One (inc b)
one-inc one = case-O one
one-inc (case-O b) = case-I b
one-inc (case-I b) = case-O (one-inc b)

can-inc : ∀ {b : Bin} → Can b → Can (inc b)
can-inc zero = from-one one
can-inc (from-one cb) = from-one (one-inc cb)

can-to-n : ∀ (n : ℕ) → Can (to n)
can-to-n zero = zero
can-to-n (suc n) = can-inc (can-to-n n)

n+n≡2*n : ∀ (n : ℕ) → n + n ≡ 2 * n
n+n≡2*n zero = refl
n+n≡2*n (suc n)
  rewrite +-identityʳ n = refl

can-id : ∀ {b : Bin} → Can b → to (from b) ≡ b
can-id zero = refl
can-id (from-one one) = refl
can-id {b O} (from-one (case-O x)) = {!!}
can-id {b I} (from-one (case-I x)) = {!!}

module ≤-Reasoning where
  infix  1 ≤-begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _≤∎

  ≤-begin_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  ≤-begin_ x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _≤∎ : ∀ (x : ℕ) → x ≤ x
  x ≤∎ = ≤-refl

open ≤-Reasoning

+-monoʳ-≤' : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤' zero p q p≤q =
  ≤-begin
    zero + p
  ≤⟨ p≤q ⟩
    zero + q
  ≤∎
+-monoʳ-≤' (suc n) p q p≤q =
  ≤-begin
    (suc n) + p
  ≤⟨ s≤s (+-monoʳ-≤' n p q p≤q) ⟩
    (suc n) + q
  ≤∎

+-monoˡ-<' : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-<' m n p m<n = {!!}

+-mono-<' : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-<' m n p q m<n p<q = {!!}
