module ch2.Lambda where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

Id : Set
Id = String

infix  5 ƛ_⇒_
infix  5 μ_⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_

data Term : Set where
  `_                       : Id → Term
  ƛ_⇒_                    : Id → Term → Term
  _·_                      : Term → Term → Term
  `zero                    : Term
  `suc_                    : Term → Term
  case_[zero⇒_|suc_⇒_]   : Term → Term → Id → Term → Term
  μ_⇒_                    : Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

sucᶜ' : Term
sucᶜ' = ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "n" · ` "s" · ` "z")

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ `zero
          |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n")]

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · (` "n" · ` "s") · ` "z"

expᶜ : Term
expᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ((` "n" · ` "m") · ` "s") · ` "z"

ƛ'_⇒_ : Term → Term → Term
ƛ' (` x) ⇒ N  =  ƛ x ⇒ N
ƛ' _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case'_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case' L [zero⇒ M |suc (` x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]
case' _ [zero⇒ _ |suc _ ⇒ _ ]     = ⊥-elim impossible
  where postulate impossible : ⊥

μ'_⇒_ : Term → Term → Term
μ' (` x) ⇒ N = μ x ⇒ N
μ' _ ⇒ _     = ⊥-elim impossible
  where postulate impossible : ⊥

plus' : Term
plus' = μ' + ⇒ ƛ' m ⇒ ƛ' n ⇒
           case' m
             [zero⇒ n
             |suc m ⇒ `suc (+ · m · n) ]
    where
    + = ` "+"
    m = ` "m"
    n = ` "n"

mul' : Term
mul' = μ' * ⇒ ƛ' m ⇒ ƛ' n ⇒
          case' m
            [zero⇒ `zero
            |suc m ⇒ plus' · n · (* · m · n) ]
    where
    * = ` "*"
    m = ` "m"
    n = ` "n"

data Value : Term → Set where
  V-ƛ : ∀ {x N} → Value (ƛ x ⇒ N)

  V-zero : Value `zero

  V-suc : ∀ {V}
    → Value V
    → Value (`suc V)

infix 9 _[_:=_]
infix 9 _⟦¬_⁇_:=_⟧
_[_:=_] : Term → Id → Term → Term

_⟦¬_⁇_:=_⟧ : {A : Set} → Term → Dec A → Id → Term → Term
N ⟦¬ yes _ ⁇ y := V ⟧ = N
N ⟦¬ no  _ ⁇ y := V ⟧ = N [ y := V ]


(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x
(ƛ x ⇒ N) [ y := V ] = ƛ x ⇒ N ⟦¬ x ≟ y ⁇ y := V ⟧
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ] = `zero
(`suc M) [ y := V ] = `suc (M [ y := V ])
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] =
  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ⟦¬ x ≟ y ⁇ y := V ⟧ ]
(μ x ⇒ N) [ y := V ] = μ x ⇒ N ⟦¬ x ≟ y ⁇ y := V ⟧
