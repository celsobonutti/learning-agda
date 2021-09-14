module ch1.Lists where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; +-comm; *-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import ch1.Isomorphism using (_≃_; _⇔_; extensionality)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys =
  begin
    length (x ∷ xs ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) = refl
reverse-++-distrib (x ∷ xs) ys
  rewrite reverse-++-distrib xs ys |
          ++-assoc (reverse ys) (reverse xs) ([ x ]) = refl

reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    x ∷ reverse (reverse xs)
  ≡⟨ cong (x ∷_) (reverse-involutive xs) ⟩
   x ∷ xs
  ∎

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨ shunt-reverse xs (x ∷ ys)⟩
    reverse xs ++ x ∷ ys
  ≡⟨⟩
    reverse xs ++ [ x ] ++ ys
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ∎

reverse' : ∀ {A : Set} → List A → List A
reverse' xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse' xs ≡ reverse xs
reverses [] = refl
reverses (x ∷ xs) =
  begin
    reverse' (x ∷ xs)
  ≡⟨ shunt-reverse xs [ x ] ⟩
    reverse xs ++ [ x ]
  ∎

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C)
  → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality (helper f g)
  where
    helper : ∀ {A B C : Set} (f : A → B) (g : B → C) (x : List A)
      → map (g ∘ f) x ≡ (map g ∘ map f) x
    helper f g [] = refl
    helper f g (x ∷ xs) =
      begin
        map (g ∘ f) (x ∷ xs)
      ≡⟨⟩
        (g ∘ f) x ∷ map (g ∘ f) xs
      ≡⟨ cong ((g ∘ f) x ∷_) (helper f g xs)  ⟩
        g (f x) ∷ map g (map f xs)
      ∎

map-++-distribute : ∀ {A B : Set} (f : A → B) (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys rewrite map-++-distribute f xs ys = refl

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node left x right) = node (map-Tree f g left) (g x) (map-Tree f g right)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

sum : List ℕ → ℕ
sum = foldr _+_ 0

foldr-∷ : ∀ {A : Set} (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) rewrite foldr-∷ xs = refl

product : List ℕ → ℕ
product = foldr _*_ 1

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys rewrite foldr-++ _⊗_ e xs ys = refl

foldr-++' : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
foldr-++' [] ys = refl
foldr-++' (x ∷ xs) ys rewrite foldr-++' xs ys = refl

map-is-foldr : ∀ {A B : Set} (f : A → B)
  → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {A} {B} f = extensionality helper
  where
    helper : (ys : List A) → map f ys ≡ foldr (λ x xs → f x ∷ xs) [] ys
    helper [] = refl
    helper (y ∷ ys) rewrite helper ys = refl

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node left x right) = g (fold-Tree f g left) x (fold-Tree f g right)


map-is-fold-Tree : ∀ {A B C D : Set} (f : A → C) (g : B → D)
  → map-Tree f g ≡ fold-Tree
                     (λ x → leaf (f x))
                     (λ left x right → node left (g x) right)
map-is-fold-Tree {A} {B} {C} {D} f g = extensionality helper
  where
    helper : ∀ (tree : Tree A B) →  map-Tree f g tree ≡ fold-Tree
                     (λ x → leaf (f x))
                     (λ left x right → node left (g x) right) tree
    helper (leaf x) = refl
    helper (node left x right)
           rewrite helper left |
                   helper right = refl


downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

sum-∷ : ∀ (x : ℕ) (xs : List ℕ)
  → sum (x ∷ xs) ≡ x + sum xs
sum-∷ x [] = refl
sum-∷ x (x₁ ∷ xs) = refl


*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p |
          sym (+-assoc p (m * p) (n * p)) = refl

+∸*-cancel : ∀ (n : ℕ) → n + (n ∸ 1) * n ≡ n * n
+∸*-cancel zero = refl
+∸*-cancel (suc n) = refl

sum-downFrom : ∀ (n : ℕ)
  → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) =
  begin
    sum (downFrom (suc n)) * 2
  ≡⟨⟩
    sum (n ∷ downFrom n) * 2
  ≡⟨ cong (_* 2) (sum-∷ n (downFrom n)) ⟩
    (n + sum (downFrom n)) * 2
  ≡⟨ *-distrib-+ n (sum (downFrom n)) 2 ⟩
    n * 2 + sum (downFrom n) * 2
  ≡⟨ cong (n * 2 +_) (sum-downFrom n) ⟩
    n * 2 + n * (n ∸ 1)
  ≡⟨ cong (_+ n * (n ∸ 1)) (*-comm n 2) ⟩
    2 * n + n * (n ∸ 1)
  ≡⟨ cong (2 * n +_) (*-comm n (n ∸ 1)) ⟩
    2 * n + (n ∸ 1) * n
  ≡⟨ sym (*-distrib-+ 2 (n ∸ 1) n) ⟩
    (2 + (n ∸ 1)) * n
  ≡⟨ cong (n +_) (+∸*-cancel n) ⟩
    (suc n) * n
  ∎

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y rewrite identityˡ ⊗-monoid y = refl
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y
  rewrite foldr-monoid _⊗_ e ⊗-monoid xs y |
          sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) = refl

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys
  rewrite foldr-++ _⊗_ e xs ys |
          foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) = refl

foldl : ∀ {A B : Set} → (B → A → B) → B → (List A) → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ (foldl _⊗_ e xs)
foldl-monoid _⊗_ e ⊗-monoid [] y rewrite (identityʳ ⊗-monoid y) = refl
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldl _⊗_ (y ⊗ x) xs
  ≡⟨ foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x) ⟩
    ((y ⊗ x) ⊗ foldl _⊗_ e xs)
  ≡⟨ assoc ⊗-monoid y x (foldl _⊗_ e xs) ⟩
    y ⊗ (x ⊗ (foldl _⊗_ e xs))
  ≡⟨ cong (y ⊗_) (sym (foldl-monoid _⊗_ e ⊗-monoid xs x)) ⟩
    y ⊗ foldl _⊗_ x xs
  ≡⟨ cong (λ n → y ⊗ foldl _⊗_ n xs) (sym (identityˡ ⊗-monoid x)) ⟩
    (y ⊗ foldl _⊗_ (e ⊗ x) xs)
  ∎

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl {A} _⊗_ e ⊗-monoid = extensionality helper
  where
    helper : (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
    helper [] = refl
    helper (x ∷ xs) =
      begin
        foldr _⊗_ e (x ∷ xs)
      ≡⟨ cong (x ⊗_) (helper xs) ⟩
        x ⊗ foldl _⊗_ e xs
      ≡⟨ sym (foldl-monoid _⊗_ e ⊗-monoid xs x) ⟩
        foldl _⊗_ x xs
      ≡⟨ cong (λ n → foldl _⊗_ n xs) (sym (identityˡ ⊗-monoid x)) ⟩
        foldl _⊗_ (e ⊗ x) xs
      ∎
