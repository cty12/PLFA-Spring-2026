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
open import lecture-notes-Lambda using (Term; ƛ_⇒_; _·_; `_; _⊢_⦂_; ⊢ƛ; ⊢`; ∅; _⇒_)
                                 renaming (Z to here; S to there)

-- The Church encoding of two: λf. λx. f (f x)
twoᶜ : Term
twoᶜ = ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "f" · ` "x")

⊢twoᶜ : ∀ {A} → ∅ ⊢ twoᶜ ⦂ (A ⇒ A) ⇒ A ⇒ A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where
  ∋s = there (λ ()) here
  ∋z = here
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
```

## Renaming

```
ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```

```
rename : ∀ {Γ Δ A}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → Γ ⊢ A
    ------------------
  → Δ ⊢ A
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
```

## Simultaneous Substitution

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

This definition of substitution works even with full beta.

```
exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)
```

```
subst : ∀ {Γ Δ A}
  → (σ : ∀ {A} → Γ ∋ A → Δ ⊢ A)
  → Γ ⊢ A
    ---------------
  → Δ ⊢ A
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
```

## Single substitution

```
_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst σ N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x
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
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]
```

## Multi-step reduction

```
infix  2 _—↠_
infix  1 begin_
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

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```

```
—↠-trans : ∀{Γ}{A}{M N L : Γ ⊢ A} → M —↠ N → N —↠ L → M —↠ L
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
    -----------
  → Steps L
eval zero    L                =  steps (L ∎) out-of-gas
eval (suc m) L
    with progress L
... | done VL                 =  steps (L ∎) (done VL)
... | step {M} L—→M
        with eval m M
...     | steps M—↠N fin    =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```
