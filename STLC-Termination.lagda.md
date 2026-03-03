```
{-# OPTIONS --rewriting #-}

module STLC-Termination where
```

# A proof that all STLC programs terminate

## Imports

```
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
 using (_≡_; refl; sym; cong; cong₂)

open import lecture-notes-Substitution
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

  step—→ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M —↠ N
    → L —→ M
      ------
    → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

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

infixr 2 _—↠⟨_⟩_
_—↠⟨_⟩_ : ∀ {Γ}{A}(L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —↠ M
    → M —↠ N
      ------
    → L —↠ N
L —↠⟨ LM ⟩ MN = —↠-trans LM MN
```

## Termination via Logical Relations

We define a predicate `ℰ A M` for terms that are well-behaved
according to type `A`. In particular, they are
terms that halt and produce a value, and furthermore the value must
behave according to its type `A`.  So the definition of ℰ is mutually
recursive with another predicate `𝒱 A V` that specifies the well-behaved
values..

```
ℰ : (A : Type) → ∅ ⊢ A → Set
𝒱 : (A : Type) → ∅ ⊢ A → Set

ℰ A M = Σ[ V ∈ ∅ ⊢ A ] (M —↠ V) × (Value V) × (𝒱 A V)
```

The predicate 𝒱 for type ℕ says the value must be a natural number, but
`𝒱 (A ⇒ B)` is more interesting. It says the value must be a
`ƛ N` where `N[ V ]` is a term that is well-behaved according to type `B`,
that is, `ℰ B (N [ V ])` for any value `V` provided that it behaves
according to type `A`, that is, `𝒱 A V`.

```
𝒱 `ℕ `zero = ⊤
𝒱 `ℕ (L · M) = ⊥
𝒱 (A ⇒ B) (ƛ N) = ∀ (V : ∅ ⊢ A) → 𝒱 A V → ℰ B (N [ V ])
𝒱 (A ⇒ B) (L · M) = ⊥
```

The well-behaved values (𝒱) are indeed values.

```
𝒱→Value : ∀{A}{M : ∅ ⊢ A} → 𝒱 A M → Value M
𝒱→Value {`ℕ} {`zero} wtv = V-zero
𝒱→Value {A ⇒ B} {ƛ N} wtv = V-ƛ
```

The 𝒱 function implies the ℰ function.
(A well-behaved value is a well-behaved term.)

```
𝒱→ℰ : ∀{A}{M : ∅ ⊢ A} → 𝒱 A M → ℰ A M
𝒱→ℰ {A}{M} wtv = ⟨ M , ⟨ M ∎ , ⟨ 𝒱→Value {A} wtv , wtv ⟩ ⟩ ⟩
```

### Compatibility lemma about reduction

```
app-compat : ∀{A}{B} {L L'  : ∅ ⊢ A ⇒ B}{M M' : ∅ ⊢ A}
           → L —↠ L'
           → Value L'
           → M —↠ M'
           → L · M —↠ L' · M'
app-compat {A}{B}{L}{L}{M}{M} (L ∎) vL (M ∎) = L · M ∎
app-compat {A}{B}{L}{L}{M}{M''} (L ∎) vL (step—→ M {M'} M'→M'' M→M') =
  begin
     L · M     —→⟨ ξ-·₂ vL M→M' ⟩
     L · M'    —↠⟨ app-compat (L ∎) vL M'→M'' ⟩
     L · M''
  ∎
app-compat {A}{B}{L}{L''}{M}{M'}(step—→ L {L'}{L''} L'→L'' L→L' ) vL' M→M' =
  begin
    L · M             —→⟨ ξ-·₁ L→L' ⟩
    L' · M            —↠⟨ app-compat L'→L'' vL' M→M' ⟩
    L'' · M'
  ∎
```

### A technical lemma about extending substitutions


We define the well-behaved substitutions σ to be the ones
that map variables in Γ to well-behaved values.

```
_⊢ˢ_ : (Γ : Context) → (Γ →ˢ ∅) → Set
Γ ⊢ˢ σ = (∀ {C : Type} (x : Γ ∋ C) → 𝒱 C (σ x))
```

We can extend a well-behaved substitution σ with another
well-behaved value V.

```
extend-sub : ∀{A}{V : ∅ ⊢ A}{Γ}{σ : Γ →ˢ ∅}
         → 𝒱 A V   →   Γ ⊢ˢ σ
         → (Γ , A) ⊢ˢ (V • σ)
extend-sub {A} {V} wtv ⊢σ {C} Z = wtv
extend-sub {A} {V} wtv ⊢σ {C} (S ∋x) = ⊢σ ∋x
```

### The fundemantal property of the logical relation

```
fundamental-property : ∀ {A}{Γ} {σ : Γ →ˢ ∅}
  → (M : Γ ⊢ A)
  → Γ ⊢ˢ σ
  → ℰ A (subst σ M)
fundamental-property {A} (` ∋x) ⊢σ = 𝒱→ℰ {A} (⊢σ ∋x)

fundamental-property {A ⇒ B}{Γ}{σ} (ƛ N) ⊢σ =
   ⟨ subst σ (ƛ N) , ⟨ ƛ (subst (exts σ) N) ∎ , ⟨ V-ƛ , IH ⟩ ⟩ ⟩
   where
   IH : (V : ∅ ⊢ A) → 𝒱 A V → ℰ B (subst (exts σ) N [ V ])
   IH V wtv = fundamental-property {B}{Γ , A}{V • σ} N (extend-sub wtv ⊢σ)

fundamental-property {B}{Γ}{σ} (_·_{A = A} L M) ⊢σ 
    with fundamental-property {A ⇒ B}{Γ}{σ} L ⊢σ
... | ⟨ L' , ⟨ L→L' , ⟨ vL' , wtvL' ⟩ ⟩ ⟩
    with vL'
... | V-ƛ{N = N}
    with fundamental-property M ⊢σ
... | ⟨ M' , ⟨ M→M' , ⟨ vM' , wtvM' ⟩ ⟩ ⟩
    with wtvL' M' wtvM'
... | ⟨ V , ⟨ →V , ⟨ vV , wtvV ⟩ ⟩ ⟩ =
      ⟨ V , ⟨ R , ⟨ vV , wtvV ⟩ ⟩ ⟩
    where
    R : subst σ L · subst σ M —↠ V
    R =   begin
          subst σ L · subst σ M     —↠⟨ app-compat L→L' vL' M→M' ⟩
          (ƛ N) · M'                —→⟨ β-ƛ vM' ⟩
          N [ M' ]                  —↠⟨ →V ⟩
          V                         ∎
 
fundamental-property {A} `zero ⊢σ = 𝒱→ℰ {`ℕ} tt
```

All STLC programs terminate.

```
terminate : ∀ {A}
  → (M : ∅ ⊢ A)
  → Σ[ V ∈ ∅ ⊢ A ] (M —↠ V) × Value V
terminate {M} ⊢M
    with fundamental-property {σ = id} ⊢M (λ ())
... | ⟨ V , ⟨ M—↠V , ⟨ vV , 𝒱V ⟩ ⟩ ⟩ =
      ⟨ V , ⟨ M—↠V , vV ⟩ ⟩
```

