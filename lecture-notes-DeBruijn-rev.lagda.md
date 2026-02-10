```
module lecture-notes-DeBruijn-rev where
```

# STLC using de Bruijn indices and intrinsically typed terms

## Imports

```
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
                         renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
```

## Intro

```
module Intro where
  open import lecture-notes-Lambda using (Term; ƛ_⇒_; _·_; `_; _⊢_⦂_; ⊢ƛ; ⊢`; ∅; _⇒_)
                                 renaming (Z to here; S to there)

  -- The Church encoding of two:
  --                 (names)  λf. λx. f (f x)
  --             (de Bruijn)  λ.  λ.  1 (1 0)
  twoᶜ : Term
  twoᶜ = ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "f" · ` "x")

  ⊢twoᶜ : ∀ {A} → ∅ ⊢ twoᶜ ⦂ (A ⇒ A) ⇒ A ⇒ A
  ⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋f · (⊢` ∋f · ⊢` ∋x)))
    where
    ∋f = there (λ ()) here
    ∋x = here
```

The term and its typing derivation are in close correspondence:

- `_ corresponds to ⊢`
- ƛ_⇒_ corresponds to ⊢ƛ
- _·_ corresponds to _·_

Further, the lookup derivation for each variable corresponds to
a number which tells us how many enclosing binders to count to
find the binding of that variable.

## Syntax

```
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infix  9 `_
infix  9 S_
```

## Types

```
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type
```

## Contexts

```
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

## Variables

```
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
```

## Intrinsically Typed Terms

```
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

-- λf. λx. f (f x)
⊢twoᶜ′ : ∀ {A : Type} → ∅ ⊢ (A ⇒ A) ⇒ A ⇒ A
⊢twoᶜ′ = ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))
```

## Renaming

```
_→ʳ_ : Context → Context → Set
Γ →ʳ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

ext : ∀ {Γ Δ A}
  → Γ →ʳ Δ
    ---------------------------------
  → (Γ , A) →ʳ (Δ , A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```

```
rename : ∀ {Γ Δ A}
  → (ρ : Γ →ʳ Δ)
  → Γ ⊢ A
    ------------------
  → Δ ⊢ A
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
```

## Simultaneous Substitution

```
_→ˢ_ : Context → Context → Set
Γ →ˢ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A
```

This definition of substitution works even with full beta.

```
{-
+------------------------+
|                        |<- σ
|  λ------------+        |
|  | ... (x+1)  |<- σ′   |
|  +------------+        |
|      ... (x)           |
+------------------------+

x    σ(x)           x   σ′(x)
0 ↦   M₀           0 ↦    0
1 ↦   M₁           1 ↦  ⇑ M₀
2 ↦   M₂           2 ↦  ⇑ M₁
  ...                 ...
  where ⇑ increments each free variable by one, while leaving each bound variable unchanged

exts(σ) = σ′
-}

⇑_ : ∀ {Γ A B} → Γ ⊢ A → Γ , B ⊢ A
⇑ M = rename S_ M
-- S_ : Γ ∋ A → Γ , B ∋ A

exts : ∀ {Γ Δ A}
  → Γ →ˢ Δ
    ---------------------------------
  → (Γ , A) →ˢ (Δ , A)
exts σ Z      =  ` Z
exts σ (S x)  =  ⇑ σ x   -- σ′ = ⇑ ∘ σ ∘ sub1

subst : ∀ {Γ Δ A}
  → (σ : Γ →ˢ Δ)
  → Γ ⊢ A
    ---------------
  → Δ ⊢ A

subst σ (` x) = σ x
subst σ (ƛ M) = ƛ subst (exts σ) M
subst σ (M · N) = subst σ M · subst σ N
subst σ `zero = `zero
```

## Single substitution

```

_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst σ₀ N
  where
  σ₀ : (Γ , B) →ˢ Γ
  σ₀ Z = M
  σ₀ (S x) = ` x

```

## Values

```
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})
```

## Reduction

```
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      ------------------------
    → (ƛ N) · W —→ N [ W ]
```

## Multi-step reduction

```
infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

```

```
—↠-trans : ∀{Γ} {A} {M N L : Γ ⊢ A}
  → M —↠ N
  → N —↠ L
    ---------------
  → M —↠ L
—↠-trans (M ∎) N—↠L = N—↠L
—↠-trans (L —→⟨ L—→M ⟩ M—↠N) N—↠L =
  let IH = —↠-trans M—↠N N—↠L in
  L —→⟨ L—→M ⟩ IH
```

## Type Safety

Preservation is already proved. Review the type signature
of the reduction relation.


```
data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
```

```
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ N)                   =  done V-ƛ
progress (L · M)
    with progress L
... | step L—→L′               =  step (ξ-·₁ L—→L′)
... | done V-ƛ
        with progress M
...     | step M—→M′           =  step (ξ-·₂ V-ƛ M—→M′)
...     | done VM                =  step (β-ƛ VM)
progress (`zero)                 =  done V-zero
```

## Evaluation

```
data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N
```

The `Steps` predicate says that a term reduced until finished.

```
data Steps : ∀ {A} → ∅ ⊢ A → Set where

  steps : ∀ {A} {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
```

The `eval` function reduces a term until the gas runs out
or until the term becomes a value.

```
Gas = ℕ

eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    ------------
  → Steps L
eval zero    L                =  steps (L ∎) out-of-gas
eval (suc m) L
    with progress L
... | done VL                 =  steps (L ∎) (done VL)
... | step {M} L—→M
        with eval m M
...     | steps M—↠N fin    =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

-- example: evaluate (λf. f 0) (λx. x)
⊢L : ∅ ⊢ `ℕ
⊢L = (ƛ ` Z · `zero) · (ƛ ` Z)

_ : eval 42 ⊢L ≡
      steps (_ —→⟨ β-ƛ V-ƛ ⟩
             _ —→⟨ β-ƛ V-zero ⟩
             _ ∎)    -- reduction steps
      (done V-zero)  -- result
_ = refl
```
