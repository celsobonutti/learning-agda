module ch2.Lambda where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_)
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

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L' M}
    → L —→ L'
    --------------------
    → L · M —→ L' · M

  ξ-·₂ : ∀ {V M M'}
    → Value V
    → M —→ M'
    --------------------
    → V · M —→ V · M'

  β-ƛ : ∀ {x N V}
    → Value V
    -----------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M'}
    → M —→ M'
    ---------------------
    → `suc M —→ `suc M'

  ξ-case : ∀ {x L L' M N}
    → L —→ L'
    ---------------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L' [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
    -----------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
  -----------
  → M —↠ N
begin M—↠N = M—↠N

postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
    ---------------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
    ---------------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

postulate
  deterministic : ∀ {L M N}
    → L —↠ M
    → L —↠ N
    --------
    → M ≡ N

_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
  ∎

one : Term
one = `suc `zero

_ : plus · one · one —↠ `suc `suc `zero
_ =
  begin
    plus · one · one
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (plus · ` "m" · ` "n")])
        · one · one
  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "n" ⇒
      case one [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · `"n")])
      · one
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    case one [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one)]
  —→⟨ β-suc V-zero ⟩
    `suc (plus · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc
    ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]) · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
    `suc
    ((ƛ "n" ⇒
      case `zero
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]) · one)
  —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
    `suc
      (case `zero
        [zero⇒ one
        |suc "m" ⇒ `suc (plus · ` "m" · one)])
  —→⟨ ξ-suc (β-zero) ⟩
    `suc `suc `zero
  ∎

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `N : Type
