module ch1.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) x = g ( f x )

_∘'_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘' f) = λ x → g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g


_+'_ : ℕ → ℕ → ℕ
m +' zero = m
m +' suc n = suc (m +' n)

same-app : ∀ (m n : ℕ) → m +' n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
    helper : ∀ (m n : ℕ) → m +' n ≡ n + m
    helper m zero = refl
    helper m (suc n) = cong suc (helper m n)

same : _+'_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

open _≃_

≃-refl : ∀ {A : Set}
  → A ≃ A
≃-refl =
  record
    { to = λ {x → x}
    ; from = λ {y → y}
    ; from∘to = λ {x → refl}
    ; to∘from = λ {y → refl}
    }

≃-sym : ∀ {A B : Set}
  → A ≃ B
  → B ≃ A
≃-sym A≃B =
  record
    { to = from A≃B
    ; from = to A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
  -------
  → A ≃ C
≃-trans A≃B B≃C =
  record
    { to = to B≃C ∘ to A≃B
    ; from = from A≃B ∘ from B≃C
    ; from∘to = λ{ x →
              begin
                (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
              ≡⟨⟩
                from A≃B (from B≃C (to B≃C (to A≃B x)))
              ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
                from A≃B (to A≃B x)
              ≡⟨ from∘to A≃B x ⟩
                x
              ∎ }
    ; to∘from = λ { y →
              begin
                (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
              ≡⟨⟩
                to B≃C (to A≃B (from A≃B (from B≃C y)))
              ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
                to B≃C (from B≃C y)
              ≡⟨ to∘from B≃C y ⟩
                y
              ∎ }
    }
