module ch1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-comm; +-assoc; +-suc; +-identityʳ)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import ch1.Isomorphism using (_≃_; extensionality)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ f → ⟨ (λ x → proj₁(f x)) , (λ y → proj₂ (f y)) ⟩
    ; from = λ{ ⟨ f , g ⟩ → λ a → ⟨ f a , g a ⟩}
    ; from∘to = λ f → refl
    ; to∘from = λ{ ⟨ f , g ⟩ → refl}
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) = λ x → inj₁ (f x)
⊎∀-implies-∀⊎ (inj₂ g) = λ y → inj₂ (g y)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  extensionality-dep : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g

∀-× : {B : Tri → Set} →
  (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× =
  record
    { to = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
    ; from = λ{ ⟨ faa , ⟨ fbb , fcc ⟩ ⟩ → λ{ aa → faa
                                            ; bb → fbb
                                            ; cc → fcc
                                            }
              }
    ; from∘to = λ{f → extensionality-dep λ{ aa → refl
                                           ; bb → refl
                                           ; cc → refl
                                           }
                 }
    ; to∘from = λ{ ⟨ faa , ⟨ fbb , fcc ⟩ ⟩ → refl}
    }

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B


Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ' (A : Set) (B : A → Set) : Set where
  field
    proj₁' : A
    proj₂' : B proj₁'

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to = λ f → λ{ ⟨ x , y ⟩ → f x y }
    ; from = λ g → λ{ a b → g ⟨ a , b ⟩ }
    ; from∘to = λ f → refl
    ; to∘from = λ g → extensionality λ{ ⟨ x , y ⟩ → refl }
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = λ{ ⟨ a , inj₁ x ⟩ → inj₁ ⟨ a , x ⟩
            ; ⟨ a , inj₂ y ⟩ → inj₂ ⟨ a , y ⟩
            }
    ; from = λ{ (inj₁ ⟨ a , x ⟩) → ⟨ a , inj₁ x ⟩
              ; (inj₂ ⟨ a , y ⟩) → ⟨ a , inj₂ y ⟩
              }
    ; from∘to = λ{ ⟨ a , inj₁ x ⟩ → refl
                 ; ⟨ a , inj₂ y ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ a , x ⟩) → refl
                 ; (inj₂ ⟨ a , y ⟩) → refl
                 }
    }


∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , ⟨ fst , snd ⟩ ⟩ = ⟨ ⟨ a , fst ⟩ , ⟨ a , snd ⟩ ⟩

∃-× : {B : Tri → Set} →
  ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-× =
  record
    { to = λ{ ⟨ aa , x₁ ⟩ → inj₁ x₁
            ; ⟨ bb , x₁ ⟩ → inj₂ (inj₁ x₁)
            ; ⟨ cc , x₁ ⟩ → inj₂ (inj₂ x₁)
            }
    ; from = λ{ (inj₁ x) → ⟨ aa , x ⟩
              ; (inj₂ (inj₁ x)) → ⟨ bb , x ⟩
              ; (inj₂ (inj₂ y)) → ⟨ cc , y ⟩
              }
    ; from∘to = λ{ ⟨ aa , x₁ ⟩ → refl
                 ; ⟨ bb , x₁ ⟩ → refl
                 ; ⟨ cc , x₁ ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ x) → refl
                 ; (inj₂ (inj₁ x)) → refl
                 ; (inj₂ (inj₂ y)) → refl
                 }
    }

data even : ℕ → Set
data odd : ℕ → Set

data even where
  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} → odd  n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ 0 , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd-suc e)   with even-∃ e
...                    | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc m , refl ⟩ = even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd ⟨ m , refl ⟩ = odd-suc (∃-even ⟨ m , refl ⟩)


∃-even' : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
∃-odd'  : ∀ {n : ℕ} → ∃[ m ] (1 + 2 * m ≡ n) →  odd n

∃-even' ⟨ zero , refl ⟩ = even-zero
∃-even' ⟨ suc m , refl ⟩ = even-suc (∃-odd' ⟨ m , sym(+-suc m (m + zero)) ⟩)
∃-odd' ⟨ m , refl ⟩ = odd-suc (∃-even' ⟨ m , refl ⟩)

∃-+-≤ : ∀ {x y z : ℕ} → y ≤ z → ∃[ x ] (x + y ≡ z)
∃-+-≤ {_} {_} {z} z≤n = ⟨ z , +-identityʳ z ⟩
∃-+-≤ {_} {suc m} (s≤s y≤z) with (∃-+-≤ y≤z)
...                              | ⟨ x , refl ⟩ = ⟨ x , +-suc x m ⟩

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to = λ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩
    ; from = λ{¬∃xy ⟨ x , y ⟩ → ¬∃xy x y}
    ; from∘to = λ{¬∃xy → extensionality-dep λ{ ⟨ x , y ⟩ → refl}}
    ; to∘from = λ _ → refl
    }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , y ⟩ = λ{f → y (f x)}

{-
  The converse does not hold because the negation of an universal
  does not mean that an existential will not hold. In other words,
  knowing that a property does not hold for _every_ value does not
  mean that it won't hold for _some_ value.
-}
