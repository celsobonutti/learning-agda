module ch1.Decidable where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import ch1.Relations using (_<_; z<s; s<s)
open import ch1.Isomorphism using (_⇔_)

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n      = true
suc m ≤ᵇ zero  = false
suc m ≤ᵇ suc n = m ≤ᵇ n

T : Bool → Set
T true  = ⊤
T false = ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt = refl

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n tt = z≤n
≤ᵇ→≤ (suc m) zero ()
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? y = yes z≤n
suc x ≤? zero = no ¬s≤z
suc x ≤? suc y with x ≤? y
...                 | yes m≤n = yes (s≤s m≤n)
...                 | no ¬m≤n = no (¬s≤s ¬m≤n)

¬m<z : ∀ {m : ℕ} → ¬ (m < zero)
¬m<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
m <? zero = no ¬m<z
zero <? suc y = yes z<s
suc x <? suc y with x <? y
...                 | yes m<n = yes (s<s m<n)
...                 | no ¬m<n = no (¬s<s ¬m<n)

m≡n→sm≡sn : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
m≡n→sm≡sn refl = refl

sm≡sn→m≡n : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
sm≡sn→m≡n refl = refl

¬m≡n→¬sm≡sn : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬m≡n→¬sm≡sn ¬m≡n = λ{sm≡sn → ¬m≡n (sm≡sn→m≡n sm≡sn)}

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no λ ()
suc m ≡ℕ? zero = no λ ()
suc m ≡ℕ? suc n with m ≡ℕ? n
...                  | yes x = yes (m≡n→sm≡sn x)
...                  | no  y = no (¬m≡n→¬sm≡sn y)


_≤?'_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?' n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p       | _    = yes (p tt)
...        | false  | _       | ¬p   = no ¬p

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no x ⌋ = false

_≤ᵇ'_ : ℕ → ℕ → Bool
m ≤ᵇ' n = ⌊ m ≤? n ⌋

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt = x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _ = tt
fromWitness {A} {no ¬x} x = ¬x x

≤ᵇ'→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ' n) → m ≤ n
≤ᵇ'→≤ = toWitness

≤→≤ᵇ' : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ' n)
≤→≤ᵇ' = fromWitness

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _     = true
_     ∨ true  = true
false ∨ false = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y   = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y}

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no ¬x) = yes ¬x

_⊃_ : Bool → Bool → Bool
_     ⊃ true    = true
false ⊃ _       = true
true  ⊃ false   = false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_       →-dec yes y = yes λ _ → y
no ¬x   →-dec _     = yes λ x → ⊥-elim (¬x x)
yes x   →-dec no ¬y = no λ f → ¬y (f x)

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes _) (yes _) = refl
∧-× (yes _) (no  _) = refl
∧-× (no  _) _       = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes _)  _       = refl
∨-⊎ (no  _)  (yes _) = refl
∨-⊎ (no  _)  (no  _) = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes _) = refl
not-¬ (no  _) = refl

_iff_ : Bool → Bool → Bool
true  iff true  = true
false iff false = true
_     iff false = false
false iff _     = false

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes x ⇔-dec yes y = yes (record { from = λ{_ → x} ; to = λ{_ → y} })
no ¬x ⇔-dec no ¬y = yes (record { from = λ{y → ⊥-elim(¬y y)} ; to = λ{x → ⊥-elim(¬x x)} })
no ¬x ⇔-dec yes y = no λ{ record { to = to ; from = from } → ¬x (from y)}
yes x ⇔-dec no ¬y = no λ{ record { to = to ; from = from } → ¬y (to x)}

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes _) (yes _) = refl
iff-⇔ (no  _) (no  _) = refl
iff-⇔ (yes _) (no  _) = refl
iff-⇔ (no  _) (yes _) = refl


minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         =    m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m


_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)

True : ∀ {Q} → Dec Q → Set
True Q = T ⌊ Q ⌋

False : ∀ {Q} → Dec (¬ Q) → Set
False ¬Q = T ⌊ ¬Q ⌋

toWitnessFalse : ∀ {A : Set} {D : Dec A} → T ⌊ ¬? D ⌋ → ¬ A
toWitnessFalse {A} {yes _} f = λ _ → f
toWitnessFalse {A} {no ¬x} _ = ¬x

fromWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ A → T ⌊ ¬? D ⌋
fromWitnessFalse {A} {yes x} ¬x = ¬x x
fromWitnessFalse {A} {no _} _ = tt

