module Scratch4 where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])

Id : Set
Id = String

infix  5  ƛ_⇒_
infixl 7  _·_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term

_ = (ƛ "x" ⇒ ` "x") · `zero


data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

--(λ a. b) [a := b] = (λ a. b)
--(λ a. b) [b := a] = (λ a. a)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  ƛ x ⇒ N
... | no  _          =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]   =  L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]   =  `zero

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

-- Type System

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  here : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  there : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom 
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I 
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ


-- Type Safety

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

data IsFun : Term → Set where
  ƛ-IsFun : ∀ {x N}
      ---------------
    → IsFun (ƛ x ⇒ N)

canonical-fun : ∀{L}{A B : Type}
  → Value L
  → ∅ ⊢ L ⦂ A ⇒ B
  → IsFun L
canonical-fun V-ƛ L:AB = ƛ-IsFun

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢ƛ N:B) = done V-ƛ
progress (L:AB · M:A)
    with progress L:AB
... | step L→N = step (ξ-·₁ L→N)
... | done vL
    with progress M:A
... | step M→N = step (ξ-·₂ vL M→N)
... | done vM
    with canonical-fun vL L:AB
... | ƛ-IsFun = step (β-ƛ vM)
progress ⊢zero = done V-zero

_⊆_ : Context → Context → Set
Γ ⊆ Γ′ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ x ⦂ A

⊆-extend : ∀{Γ Γ′ x A}
  → Γ ⊆ Γ′
  → (Γ , x ⦂ A) ⊆ (Γ′ , x ⦂ A)
⊆-extend {x = y} Γ⊆Γ′ here = here
⊆-extend {x = y} Γ⊆Γ′ (there{y = y} x≢y ∋x) = there x≢y (Γ⊆Γ′ ∋x)

weaken : ∀ {Γ Γ′ M A}
  → Γ ⊢ M ⦂ A
  → Γ ⊆ Γ′
    ----------
  → Γ′ ⊢ M ⦂ A
weaken (⊢` ∋x) Γ⊆Γ′ = ⊢` (Γ⊆Γ′ ∋x)
weaken (⊢ƛ N:B) Γ⊆Γ′ = ⊢ƛ (weaken N:B (⊆-extend Γ⊆Γ′))
weaken (L:AB · M:A) Γ⊆Γ′ = (weaken L:AB Γ⊆Γ′) · (weaken M:A Γ⊆Γ′)
weaken ⊢zero Γ⊆Γ′ = ⊢zero

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → (Γ , y ⦂ B) , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → (Γ , x ⦂ A) , y ⦂ B ⊢ M ⦂ C
swap {Γ}{x}{y}{M}{A}{B}{C} x≢y M:C = weaken M:C G
  where
  G : ((Γ , y ⦂ B) , x ⦂ A) ⊆ ((Γ , x ⦂ A) , y ⦂ B)
  G {x} {C} here = there x≢y here
  G {x} {C} (there x₁ here) = here
  G {x} {C} (there x₁ (there x₂ ∋x)) = there x₂ (there x₁ ∋x)


drop : ∀ {Γ x M A B C}
  → (Γ , x ⦂ A) , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop M:C = {!!}

weaken-all : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken-all M:A = {!!}

subst : ∀ {M N : Term}{x : Id}{A B : Type}{Γ}
  → ∅ ⊢ M ⦂ A
  → (Γ , x ⦂ A) ⊢ N ⦂ B
  → Γ ⊢ N [ x := M ] ⦂ B
subst {x = y} M:A (⊢` {x = x} here)
    with x ≟ y
... | yes refl = weaken-all M:A
... | no x≢y = ⊥-elim (x≢y refl)
subst {x = y} M:A (⊢` {x = x} (there x≢y ∋x))
    with x ≟ y
... | yes refl = ⊥-elim (x≢y refl)
... | no x≢y = ⊢` ∋x
subst {M = V}{x = y} M:A (⊢ƛ{x = x} N:B)
    with x ≟ y
... | yes refl = ⊢ƛ (drop N:B)
... | no x≢y =
     let N:B′ = swap x≢y N:B in
     ⊢ƛ (subst M:A N:B′)
subst M:A (L:AB · M₁:B) = (subst M:A L:AB) · (subst M:A M₁:B)
subst M:A ⊢zero = ⊢zero

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (_·_{A = A}{B} L:AB M:A) (ξ-·₁{L′ = L′} L→L′) =
  let IH1  : ∅ ⊢ L′ ⦂ A ⇒ B
      IH1 = preserve L:AB L→L′ in
  IH1 · M:A
preserve (_·_{L = V}{A = A}{B} V:AB M:A) (ξ-·₂{M′ = M′} v M→M′) =
  let IH2  : ∅ ⊢ M′ ⦂ A
      IH2 = preserve M:A M→M′ in
  V:AB · IH2
preserve (_·_ {A = A} {B} (⊢ƛ N:B) M:A) (β-ƛ vM) = subst M:A N:B
