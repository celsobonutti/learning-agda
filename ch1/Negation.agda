module ch1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import ch1.Isomorphism using (_≃_; extensionality)
open import ch1.Relations using (_<_; inv-s<s; s<s; z<s)


¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
  → ¬ ¬ A
¬¬-intro x = λ ¬x → ¬x x

¬¬-intro' : ∀ {A : Set}
  → A
  → ¬ ¬ A
¬¬-intro' x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
  → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id' : ⊥ → ⊥
id' ()

id≡id' : id ≡ id'
id≡id' = extensionality λ ()

assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
assimilation ¬x ¬x' = extensionality λ x → ⊥-elim (¬x x)

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive {zero} = λ()
<-irreflexive {suc n} x = <-irreflexive (inv-s<s x)

infix 4 _≮_
_≮_ : ∀ (m n : ℕ) → Set
m ≮ n = ¬ (m < n)

-- trichotomy : ∀ (m n : ℕ)
--   → (m < n × m ≢ n × n ≮ m)
--   ⊎  (m ≮ n × m ≡ n × n ≮ m)
--   ⊎  (m ≮ n × m ≢ n × n < m)
-- trichotomy zero zero = inj₂ (inj₁ ((λ()) , ( refl , λ())))
-- trichotomy zero (suc n) = inj₁ (z<s , ((λ()) , λ()))
-- trichotomy (suc m) zero = inj₂ (inj₂ (((λ()) , ((λ()) , z<s ))))
-- trichotomy (suc m) (suc n) with trichotomy m n
-- ...                             | inj₁ (m<n , ( m≢n , n≮m )) = {!!}
-- ...                             | inj₂ ( inj₁ (m≮n , ( m≡n , n≮m ))) = {!!}
-- ...                             | inj₂ ( inj₂ (m≮n , ( m≢n , n<m ))) = {!!}

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
    { to = λ neg → ( (λ x → neg (inj₁ x)) , λ y → neg (inj₂ y) )
    ; from = λ ( ¬x , ¬y ) → λ { (inj₁ x) → ¬x x
                                ; (inj₂ y) → ¬y y}
    ; from∘to = λ ¬A⊎B → extensionality λ A⊎B → ⊥-elim (¬A⊎B A⊎B)
    ; to∘from = λ _ → refl
    }

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k ((inj₂ λ x → k (inj₁ x)))
