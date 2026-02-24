```
module lecture-notes-Bidirectional where

open import Data.Nat
open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.Unit
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
```

```
Id : Set
Id = ℕ

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type
  
infix  5  ƛ_
infix  5  μ_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                    :  Id → Term
  ƛ_                    :  Term → Term
  _·_                   :  Term → Term → Term
  `zero                 :  Term
  `suc_                 :  Term → Term
  case_[zero⇒_|suc⇒_]  :  Term → Term → Term → Term
  μ_                   :  Term → Term
  _⦂_                  : Term → Type → Term


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

Context : Set
Context = List Type
```

```
lookup : Context → Id → Maybe Type
lookup [] zero = nothing
lookup (A ∷ Γ) zero = just A
lookup [] (suc x) = nothing
lookup (A ∷ Γ) (suc x) = lookup Γ x
```

```
synthesize : Context → Term → Maybe Type
inherit : Context → Term → Type → Maybe ⊤
synth-and-check : Context → Term → Type → Maybe ⊤

synthesize Γ (` x) = lookup Γ x
synthesize Γ (ƛ M) = nothing
synthesize Γ (L · M)
    with synthesize Γ L
... | nothing = nothing
... | just `ℕ = nothing
... | just (A ⇒ B)
    with inherit Γ M A
... | nothing = nothing
... | just tt = just B
synthesize Γ `zero = just `ℕ
synthesize Γ (`suc M)
    with inherit Γ M `ℕ
... | nothing = nothing
... | just tt = just `ℕ
synthesize Γ case L [zero⇒ M |suc⇒ N ]
    with inherit Γ L `ℕ
... | nothing = nothing
... | just tt
    with synthesize Γ M
... | nothing = nothing
... | just A
    with inherit (`ℕ ∷ Γ) N A
... | nothing = nothing
... | just tt = just A
synthesize Γ (μ M) = nothing
synthesize Γ (M ⦂ A)
    with inherit Γ M A
... | nothing = nothing
... | just tt = just A

inherit Γ (ƛ N) (A ⇒ B)
    with inherit (A ∷ Γ) N B
... | nothing = nothing
... | just tt = just tt
inherit Γ (ƛ N) `ℕ = nothing
inherit Γ case L [zero⇒ M |suc⇒ N ] A
    with inherit Γ L `ℕ
... | nothing = nothing
... | just tt
    with inherit Γ M A
... | nothing = nothing
... | just tt
    with inherit (`ℕ ∷ Γ) N A
... | nothing = nothing
... | just tt = just tt
inherit Γ (μ N) A
    with inherit (A ∷ Γ) N A
... | nothing = nothing
... | just tt = just tt
inherit Γ (` x) A = synth-and-check Γ (` x) A
inherit Γ (L · M) B = synth-and-check Γ (L · M) B
inherit Γ `zero A = synth-and-check Γ `zero A
inherit Γ (`suc M) A = synth-and-check Γ (`suc M) A
inherit Γ (M ⦂ B) A
    with inherit Γ M B
... | nothing = nothing
... | just tt
    with A ≡? B
... | yes refl = just tt
... | no neq = nothing

synth-and-check Γ M A 
    with synthesize Γ M
... | nothing = nothing
... | just B
    with A ≡? B
... | yes refl = just tt
... | no neq = nothing
```

```
Ch : Type
Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
twoᶜ : Term
twoᶜ = (ƛ ƛ ` 1 · (` 1 · (` 0))) ⦂ Ch

_ : inherit [] twoᶜ Ch ≡ just tt
_ = refl

plusᶜ : Term
plusᶜ = (ƛ ƛ ƛ ƛ ` 3 · (` 1) · (` 2 · (` 1) · (` 0))) ⦂ (Ch ⇒ Ch ⇒ Ch)

_ : inherit [] plusᶜ (Ch ⇒ Ch ⇒ Ch) ≡ just tt
_ = refl

sucᶜ : Term
sucᶜ = ƛ `suc (` 0)

2+2ᶜ : Term
2+2ᶜ = (((plusᶜ · twoᶜ) · twoᶜ) · sucᶜ) · `zero

_ : synthesize [] 2+2ᶜ ≡ just `ℕ
_ = refl
```
