module Scratch3 where

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


-- Reduction

data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero


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

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  here : ∀ {Γ x A}
      ------------------
    → (Γ , x ⦂ A) ∋ x ⦂ A

  there : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → (Γ , y ⦂ B) ∋ x ⦂ A

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

infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

canonical : ∀ {V A}
  → ∅ ⊢ V ⦂ A
  → Value V
    ---------------
  → Canonical V ⦂ A
canonical (⊢ƛ VA) V-ƛ = C-ƛ
canonical ⊢zero vV = C-zero

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢ƛ MA)        = done V-ƛ
progress (LAB · MA)
    with progress LAB
... | step L→L′         = step (ξ-·₁ L→L′)
... | done VL
    with progress MA
... | step M→M′         = step (ξ-·₂ VL M→M′)
... | done VM
    with canonical LAB VL
... | C-ƛ                = step (β-ƛ VM)
progress ⊢zero           = done V-zero


-- Context Subset Extension
-- If Γ ⊆ Δ then (Γ, y ⦂ B) ⊆ (Δ, y ⦂ B).
ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ here = here
ext ρ (there x≢y ∋x) = there x≢y (ρ ∋x)

-- Context Weakening
-- If  Γ ⊆ Δ  and  Γ ⊢ M ⦂ A  then  Δ ⊢ M ⦂ A.
weaken : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
weaken ρ (⊢` ∋y) = ⊢` (ρ ∋y)
weaken ρ (⊢ƛ N:A) = ⊢ƛ (weaken (ext ρ) N:A)
weaken ρ (L:AB · M:A) = (weaken ρ L:AB) · (weaken ρ M:A)
weaken ρ ⊢zero = ⊢zero

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = weaken ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ here = there x≢y here
  ρ (there ne here) = here
  ρ (there ne1 (there ne2 ∋z)) = there ne2 (there ne1 ∋z)

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = weaken ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ here                 =  here
  ρ (there x≢x here)         =  ⊥-elim (x≢x refl)
  ρ (there z≢x (there _ ∋z))  =  there z≢x ∋z

weaken-all : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken-all {Γ} ⊢M = weaken ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()
  

subst : ∀ {Γ y N V A B}
   → ∅ ⊢ V ⦂ A
   → Γ , y ⦂ A ⊢ N ⦂ B
   → Γ ⊢ N [ y := V ] ⦂ B
subst {y = y} V:A (⊢` {x = y} here) with y ≟ y
... | yes refl = weaken-all V:A
... | no y≢y = ⊥-elim (y≢y refl)
subst {y = y} V:A (⊢`{x = x} (there x≢y ∋x)) with x ≟ y
... | yes refl = ⊥-elim (x≢y refl)
... | no _ = ⊢` ∋x
subst {Γ}{y}{V = V} V:A (⊢ƛ {x = x}{N}{A}{B} N:B) with x ≟ y
... | yes refl = ⊢ƛ (drop N:B)
... | no x≢y =
      let IH  : Γ , x ⦂ A ⊢ N [ y := V ] ⦂ B
          IH = subst V:A (swap x≢y N:B) in
      ⊢ƛ IH
subst V:C (L:AB · M:A) = (subst V:C L:AB) · (subst V:C M:A)
subst V:A ⊢zero = ⊢zero


preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (L:AB · M:A) (ξ-·₁ L→L′) = (preserve L:AB L→L′) · M:A
preserve (L:AB · M:A) (ξ-·₂ v M→N) = L:AB · (preserve M:A M→N)
preserve {A = B} ((⊢ƛ N:B) · V:A) (β-ƛ{V = V} v) = subst V:A N:B
