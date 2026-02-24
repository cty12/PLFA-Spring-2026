```
module lecture-notes-Bidirectional where
```

# Bidirectional Type Checking

## Imports

```
open import Data.Nat
open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.Unit
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Product using (Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
```

## Types

```
infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type
  
_≡?_ : (A B : Type) → Dec (A ≡ B)
(A₁ ⇒ A₂) ≡? (B₁ ⇒ B₂)
    with A₁ ≡? B₁
... | no neq = no λ {refl → neq refl}
... | yes refl
    with A₂ ≡? B₂
... | no neq = no λ {refl → neq refl}
... | yes refl = yes refl
(A ⇒ A₁) ≡? `ℕ = no λ ()
`ℕ ≡? (B ⇒ B₁) = no λ ()
`ℕ ≡? `ℕ = yes refl
```

## Surface Language Terms

```
infix  5  ƛ_
infix  5  μ_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

Id : Set
Id = ℕ

data Term : Set where
  `_                    :  Id → Term
  ƛ_                    :  Term → Term
  _·_                   :  Term → Term → Term
  `zero                 :  Term
  `suc_                 :  Term → Term
  case_[zero⇒_|suc⇒_]  :  Term → Term → Term → Term
  μ_                   :  Term → Term
  _⦂_                  : Term → Type → Term
```

## Target Language Terms (Intrinsic STLC)

```
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  `zero : ∀ {Γ}
      ---------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      ----------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ---------
    → Γ ⊢ A
```

## Bidirectional Type Checker and Elaborator for Surface Language

```
lookup : (Γ : Context) → (x : Id) → Maybe (∃[ A ] Γ ∋ A)
lookup ∅ x = nothing
lookup (Γ , B) zero = just ⟨ B , Z ⟩
lookup (Γ , B) (suc x)
    with lookup Γ x
... | nothing = nothing
... | just ⟨ A , ∋x ⟩ = just ⟨ A , (S ∋x) ⟩

synthesize : (Γ : Context) → (M : Term) → Maybe (∃[ A ] (Γ ⊢ A))
inherit : (Γ : Context) → (M : Term) → (A : Type) → Maybe (Γ ⊢ A)

synthesize Γ (` x)
    with lookup Γ x
... | nothing = nothing
... | just ⟨ A , ∋x ⟩ = just ⟨ A , (` ∋x) ⟩
synthesize Γ (ƛ N) = nothing
synthesize Γ (L · M)
    with synthesize Γ L
... | nothing = nothing
... | just ⟨ `ℕ , ⊢L ⟩ = nothing
... | just ⟨ A ⇒ B , ⊢L ⟩
    with inherit Γ M A
... | nothing = nothing
... | just ⊢M = just ⟨ B , (⊢L · ⊢M) ⟩
synthesize Γ `zero = just ⟨ `ℕ , `zero ⟩
synthesize Γ (`suc M)
    with inherit Γ M `ℕ
... | nothing = nothing
... | just ⊢M = just ⟨ `ℕ , `suc ⊢M ⟩
synthesize Γ case L [zero⇒ M |suc⇒ N ]
    with inherit Γ L `ℕ
... | nothing = nothing
... | just ⊢L
    with synthesize Γ M
... | nothing = nothing
... | just ⟨ A , ⊢M ⟩
    with inherit (Γ , `ℕ) N A
... | nothing = nothing
... | just ⊢N = just ⟨ A , case ⊢L ⊢M ⊢N ⟩
synthesize Γ (μ M) = nothing
synthesize Γ (M ⦂ B)
    with inherit Γ M B
... | nothing = nothing
... | just ⊢M = just ⟨ B , ⊢M ⟩

inherit Γ (ƛ N) (A ⇒ B)
    with inherit (Γ , A) N B
... | nothing = nothing
... | just ⊢N = just (ƛ ⊢N)
inherit Γ (ƛ N) `ℕ = nothing
inherit Γ case L [zero⇒ M |suc⇒ N ] A
    with inherit Γ L `ℕ
... | nothing = nothing
... | just ⊢L
    with inherit Γ M A
... | nothing = nothing
... | just ⊢M
    with inherit (Γ , `ℕ) N A
... | nothing = nothing
... | just ⊢N = just (case ⊢L ⊢M ⊢N)
inherit Γ (μ M) A
    with inherit (Γ , A) M A
... | nothing = nothing
... | just ⊢M = just (μ ⊢M)
inherit Γ M A
    with synthesize Γ M
... | nothing = nothing
... | just ⟨ B , ⊢M ⟩
    with A ≡? B
... | yes refl = just ⊢M
... | no neq = nothing
```

## Translation from STLC back to Surface Language


```
∋→ℕ : ∀{Γ A} → Γ ∋ A → ℕ
∋→ℕ Z = 0
∋→ℕ (S ∋x) = suc (∋→ℕ ∋x)

back : ∀{Γ A} → Γ ⊢ A → Term
back (` ∋x) = ` ∋→ℕ ∋x
back {Γ}{A ⇒ B} (ƛ ⊢N) = (ƛ (back{Γ , A} ⊢N)) ⦂ (A ⇒ B)
back (⊢L · ⊢M) = back ⊢L · back ⊢M
back `zero = `zero
back (`suc ⊢M) = `suc (back ⊢M )
back (case ⊢L ⊢M ⊢N) = case (back ⊢L) [zero⇒ back ⊢M |suc⇒ back ⊢N ] 
back {Γ}{A} (μ ⊢M) = (μ (back ⊢M)) ⦂ A
```

## back then synthesize/inherit is the identity

```
≡?-refl : ∀ A → A ≡? A ≡ yes refl
≡?-refl (A ⇒ B) rewrite ≡?-refl A | ≡?-refl B = refl
≡?-refl `ℕ = refl

∋→ℕ-lookup : ∀ {Γ A} (∋x : Γ ∋ A)
  → lookup Γ (∋→ℕ ∋x) ≡ just ⟨ A , ∋x ⟩ 
∋→ℕ-lookup Z = refl
∋→ℕ-lookup (S ∋x) rewrite ∋→ℕ-lookup ∋x = refl

inherit-back-id : ∀{Γ A} (⊢M : Γ ⊢ A)
  → inherit Γ (back ⊢M) A ≡ just ⊢M
  
synth-back-id : ∀{Γ A} (⊢M : Γ ⊢ A)
  → synthesize Γ (back ⊢M) ≡ just ⟨ A , ⊢M ⟩
synth-back-id {Γ}{A} (` ∋x) rewrite ∋→ℕ-lookup ∋x = refl
synth-back-id {Γ}{A ⇒ B} (ƛ ⊢N) rewrite inherit-back-id ⊢N = refl
synth-back-id (⊢L · ⊢M)
   rewrite synth-back-id ⊢L | inherit-back-id ⊢M = refl
synth-back-id `zero = refl
synth-back-id (`suc ⊢M)
   rewrite inherit-back-id ⊢M = refl
synth-back-id (case ⊢L ⊢M ⊢N)
   rewrite inherit-back-id ⊢L
   | synth-back-id ⊢M
   | inherit-back-id ⊢N = refl
synth-back-id (μ ⊢M) rewrite inherit-back-id ⊢M = refl

inherit-back-id {Γ}{A ⇒ B} (ƛ ⊢N)
    rewrite inherit-back-id ⊢N
    | ≡?-refl A | ≡?-refl (A ⇒ B) | ≡?-refl B = refl
inherit-back-id {Γ}{A} (μ ⊢N) rewrite inherit-back-id ⊢N | ≡?-refl A = refl
inherit-back-id (case ⊢L ⊢M ⊢N)
    rewrite inherit-back-id ⊢L
    | inherit-back-id ⊢M | inherit-back-id ⊢N = refl

inherit-back-id {Γ}{A} (` x)
    rewrite synth-back-id (` x) | ≡?-refl A = refl
inherit-back-id {Γ}{A} (⊢L · ⊢M)
    rewrite synth-back-id (⊢L · ⊢M) | ≡?-refl A = refl
inherit-back-id `zero = refl
inherit-back-id {Γ}{A} (`suc ⊢M)
    rewrite synth-back-id (`suc ⊢M) | ≡?-refl A = refl
```
