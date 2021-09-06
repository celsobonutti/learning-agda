module ch1.Connectives where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import ch1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open ch1.Isomorphism.≃-Reasoning
open _⇔_

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : ∀ {A B : Set}
  → A × B
  → A
proj₁ ⟨ A , _ ⟩ = A

proj₂ : ∀ {A B : Set}
  → A × B
  → B
proj₂ ⟨ _ , B ⟩ = B

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

record _×'_ (A B : Set) : Set where
  constructor ⟨_,_⟩'
  field
    proj₁' : A
    proj₂' : B

open _×'_

η-×' : ∀ {A B : Set} (w : A ×' B) → ⟨ proj₁' w , proj₂' w ⟩' ≡ w
η-×' w = refl

x-comm : ∀ {A B : Set} → A × B ≃ B × A
x-comm =
  record
    { to = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from = λ { ⟨ y , x ⟩ → ⟨ x , y ⟩}
    ; to∘from = λ { ⟨ x , y ⟩ → refl}
    ; from∘to = λ { ⟨ y , x ⟩ → refl}
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩}
    ; from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl}
    }

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ{A⇔B → ⟨ to A⇔B , from A⇔B ⟩}
    ; from = λ{⟨ A→B , B→A ⟩ →  record { to = A→B; from = B→A }}
    ; to∘from = λ{⟨ A→B , B→A ⟩ → {!!}}
    ; from∘to = {!!}
    }
