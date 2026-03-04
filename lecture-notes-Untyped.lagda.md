```
{-# OPTIONS --rewriting #-}

module lecture-notes-Untyped where
```

# Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _<_; z<s; s<s; _≤_; z≤n; s≤s; _≤?_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
```

# Syntax

First, we get all our infix declarations out of the way:

```agda
infix  6  ƛ_
infix  6  `_
infixl 7  _·_
```

# Variables

```agda
Var = ℕ
```

# Terms

```agda
data Term : Set where
  `_ : Var → Term
  ƛ_  : Term → Term
  _·_ : Term → Term → Term
```

# Renaming

```agda
Rename : Set
Rename = ℕ → ℕ
```

```agda
ext : Rename → Rename
ext ρ 0      =  0
ext ρ (suc x)  =  suc (ρ x)
```

```agda
rename : Rename → Term → Term
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
```

# Simultaneous substitution

```agda
Subst = ℕ → Term
```

Our definition of substitution is also exactly as before.
First we need an extension lemma:


```agda
exts : Subst → Subst
exts σ 0      =  ` 0
exts σ (suc x)  =  rename suc (σ x)
```

Again, we could replace all instances of `A` and `B` by `★`.

Now it is straightforward to define substitution:

```agda
subst : Subst → Term → Term
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
```

# Single substitution

It is easy to define the special case of substitution for one free variable:

```agda
subst-zero : Term → Subst
subst-zero M 0        =  M
subst-zero M (suc x)  =  ` x

_[_] : Term → Term → Term
_[_] N M =  subst (subst-zero M) N
```

# Neutral and normal terms

Reduction continues until a term is fully normalised.  Hence, instead
of values, we are now interested in _normal forms_.  Terms in normal
form are defined by mutual recursion with _neutral_ terms:

```agda
data Neutral : Term → Set
data Normal  : Term → Set
```

Neutral terms arise because we now consider reduction of open terms,
which may contain free variables.  A term is neutral if it is a
variable or a neutral term applied to a normal term:

```agda
data Neutral where

  `_  : ∀ (x : Var)
      -------------
    → Neutral (` x)

  _·_  : ∀ {L M : Term}
    → Neutral L
    → Normal M
      ---------------
    → Neutral (L · M)
```

A term is a normal form if it is neutral or an abstraction where the
body is a normal form. We use `′_` to label neutral terms.
Like `` `_ ``, it is unobtrusive:

```agda
data Normal where

  ′_ : ∀ {M : Term}
    → Neutral M
      ---------
    → Normal M

  ƛ_  : ∀ {N : Term}
    → Normal N
      ------------
    → Normal (ƛ N)
```

# Reduction step

The reduction rules are altered to switch from call-by-value to
call-by-name and to enable full normalisation:

* The rule `ξ₁` remains the same as it was for the simply-typed
  lambda calculus.

* In rule `ξ₂`, the requirement that the term `L` is a value
  is dropped. So this rule can overlap with `ξ₁` and
  reduction is _non-deterministic_. One can choose to reduce
  a term inside either `L` or `M`.

* In rule `β`, the requirement that the argument is a value
  is dropped, corresponding to call-by-name evaluation.
  This introduces further non-determinism, as `β` overlaps
  with `ξ₂` when there are redexes in the argument.

* A new rule `ζ` is added, to enable reduction underneath a lambda.

Here are the formalised rules:

```agda
infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ₁ : ∀ {L L′ M : Term}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂ : ∀ {L M M′ : Term}
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β : ∀ {N : Term} {M : Term}
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  ζ : ∀ {N N′ : Term}
    → N —→ N′
      -----------
    → ƛ N —→ ƛ N′
```

# Reflexive and transitive closure

We cut-and-paste the previous definition:

```agda
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where

  _∎ : (M : Term)
      ------
    → M —↠ M

  step—→ : (L : Term) {M N : Term}
    → M —↠ N
    → L —→ M
      ------
    → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

begin_ : ∀ {M N : Term}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```

```agda
—↠-trans : ∀{L M N : Term}
         → L —↠ M
         → M —↠ N
         → L —↠ N
—↠-trans (M ∎) mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)
```

```agda
appL-cong : ∀ {L L' M : Term}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong {L}{L'}{M} (L ∎) = L · M ∎
appL-cong {L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁ r ⟩ appL-cong rs
```

```agda
lam-cong : ∀ {N N' : Term}
         → N —↠ N'
           ---------------
         → ƛ N —↠ ƛ N'
lam-cong {N} {N'} (.N ∎) = ƛ N ∎
lam-cong {N} {N'} (.N —→⟨ r ⟩ N→N') = step—→ (ƛ N) (lam-cong N→N') (ζ r)
```
