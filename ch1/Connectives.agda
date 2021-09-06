module ch1.Connectives where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
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

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
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
    ; to∘from = λ{⟨ A→B , B→A ⟩ → refl}
    ; from∘to = λ{A⇔B →  refl}
    }

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where
  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀{A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ _) = refl
η-⊎ (inj₂ _) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ _) = refl
uniq-⊎ h (inj₂ _) = refl

infixr 1 _⊎_

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm {A} {B} =
  record
    { to = invert
    ; from = invert
    ; from∘to = η-invert
    ; to∘from = η-invert
    }
  where
    invert : ∀ {C D : Set} → C ⊎ D → D ⊎ C
    invert (inj₁ x) = inj₂ x
    invert (inj₂ y) = inj₁ y
    η-invert : ∀ {C D : Set} (w : C ⊎ D) → invert (invert w) ≡ w
    η-invert (inj₁ x) = refl
    η-invert (inj₂ x) = refl

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = ⊎-to
    ; from = ⊎-from
    ; from∘to = ⊎-from∘to
    ; to∘from = ⊎-to∘from
    }
  where
    ⊎-to : {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
    ⊎-to (inj₁ (inj₁ x)) = inj₁ x
    ⊎-to (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
    ⊎-to (inj₂ x) = inj₂ (inj₂ x)
    ⊎-from : {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
    ⊎-from (inj₁ x) = inj₁ (inj₁ x)
    ⊎-from (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
    ⊎-from (inj₂ (inj₂ x)) = inj₂ x
    ⊎-from∘to : ∀ {A B C : Set} (w : (A ⊎ B) ⊎ C) → ⊎-from (⊎-to w) ≡ w
    ⊎-from∘to (inj₁ (inj₁ x)) = refl
    ⊎-from∘to (inj₁ (inj₂ x)) = refl
    ⊎-from∘to (inj₂ x) = refl
    ⊎-to∘from : ∀ {A B C : Set} (w : A ⊎ B ⊎ C) → ⊎-to (⊎-from w) ≡ w
    ⊎-to∘from (inj₁ x) = refl
    ⊎-to∘from (inj₂ (inj₁ x)) = refl
    ⊎-to∘from (inj₂ (inj₂ x)) = refl

data ⊥ : Set where

⊥-elim : ∀ {A : Set}
  → ⊥
  → A
⊥-elim ()
