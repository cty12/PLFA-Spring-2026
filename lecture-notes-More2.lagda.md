```
{-# OPTIONS --rewriting #-}

module lecture-notes-More2 where
```

# STLC + Primitives, Let, Arrays, and Errors


## Imports

```
open import Data.Bool renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)

```

## Primitives

The idea here is to use Agda values as primitive constants. We include
natural numbers, Booleans, and Agda functions over naturals and
Booleans.

The `Base` and `Prim` data types describe the types of constants.

```
data Base : Set where
  B-Nat : Base
  B-Bool : Base

data Prim : Set where
  base : Base → Prim
  _⇒_ : Base → Prim → Prim
```

The `base-rep` and `rep` functions map from the type descriptors to
the Agda types that we will use to represent the constants.

```
base-rep : Base → Set 
base-rep B-Nat = ℕ
base-rep B-Bool = 𝔹

rep : Prim → Set
rep (base b) = base-rep b
rep (b ⇒ p) = base-rep b → rep p
```

## Types

```
data Type : Set where
  `ℕ   : Type
  Bool   : Type
  _⇒_   : Type → Type → Type
  Array _  : Type → Type
```

## Type of a primitive

```
typeof-base : Base → Type
typeof-base B-Nat = `ℕ
typeof-base B-Bool = Bool

typeof : Prim → Type
typeof (base b) = typeof-base b 
typeof (b ⇒ p) = typeof-base b ⇒ typeof p
```

## Contexts

```
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

```
infix  4  _∋_⦂_

data _∋_⦂_ : Context → ℕ → Type → Set where

  Z : ∀ {Γ A}
      ------------------
    → Γ , A ∋ 0 ⦂ A

  S : ∀ {Γ x A B}
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , B ∋ (suc x) ⦂ A
```

## Typing judgement


```
infix  4  _⊢_

data _⊢_ : Context → Type → Set where

  -- variables
  `_ : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ A

  -- ⇒-I 
  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
      ----------
    → Γ ⊢ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ------
    → Γ ⊢ B

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ---------
    → Γ ⊢ A

  $ : ∀{Γ}{A} (p : Prim) (k : rep p)
       -----------------------------
     → Γ ⊢ typeof p

  `let : ∀{Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ B

  〈〉 : ∀{Γ A}
      -----------
    → Γ ⊢ Array A

  _⦂⦂_ : ∀{Γ A}
    → Γ ⊢ A
    → Γ ⊢ Array A
      -----------
    → Γ ⊢ Array A

  _!_ : ∀{Γ A}
    → Γ ⊢ Array A
    → Γ ⊢ `ℕ
      -----------
    → Γ ⊢ A

  error : ∀ {Γ A}
      -----------
    → Γ ⊢ A
```

## Values

```
data Value : ∀{Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀{Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-const : ∀ {p k}
      -----------------
    → Value ($ p k)

  V-〈〉 : Value 〈〉

  V-⦂⦂ : ∀ {Γ A} {V : Γ ⊢ A}{Vs : Γ ⊢ Array A}
    → Value V
    → Value Vs
      -----------------
    → Value (V ⦂⦂ Vs)
```

## Frames and plug

With the addition of errors, one would need to add many more rules for
propagating an error to the top of the program. We instead collapse
these rules, and the ξ rules, into just two rules by abstracting over
the notion of a _frame_, which controls how reduction can occur inside
of each term constructor. Think of the `□` symbol is a hole in the term.

```
data Frame : ∀ (A B : Type) → Set where
  □·_ : ∀{A B C} → ∅ ⊢ A → Frame (A ⇒ B) B
  _·□ : ∀{A B C} → (M : ∅ ⊢ A ⇒ B) → (v : Value M) → Frame A B
  □⦂⦂_ : ∀{A} → ∅ ⊢ Array A → Frame A (Array A)
  _⦂⦂□ : ∀{A} → (M : ∅ ⊢ A) → (v : Value M) → Frame (Array A) (Array A)
  □!_ : ∀{A} → ∅ ⊢ `ℕ → Frame (Array A) A
  _!□ : ∀{A} → ∅ ⊢ Array A → Frame `ℕ A
  let□ : ∀{A B} → ∅ , A ⊢ B → Frame A B
```

The `plug` function fills a frame's hole with a term.

```
plug : ∀{A B} → ∅ ⊢ A → Frame A B → ∅ ⊢ B
plug L (□· M)        = L · M
plug M ((L ·□) v)    = L · M
plug M (□⦂⦂ N)       = M ⦂⦂ N
plug N ((M ⦂⦂□) v)   = M ⦂⦂ N
plug M (□! N)        = M ! N
plug N (M !□)        = M ! N
plug M (let□ N)      = `let M N
```

## Reduction

```
infix 4 _—→_

data _—→_ : ∀{A} → ∅ ⊢ A → ∅ ⊢ A → Set where

  ξ : ∀ {M M′}
    → (F : Frame)
    → M —→ M′
      ---------------------
    → plug M F —→ plug M′ F

  lift-error :
      (F : Frame)
    → plug error F —→ error

  β-ƛ : ∀ {N V}
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  β-μ : ∀ {M}
      ----------------
    → μ M —→ M [ μ M ]

  δ : ∀ {b p f k}
      ---------------------------------------------
    → ($ (b ⇒ p) f) · ($ (base b) k) —→ ($ p (f k))

  β-index-0 : ∀ {V Vs}
    → Value (V ⦂⦂ Vs)
      -------------------------
    → (V ⦂⦂ Vs) ! ($ _ 0) —→  V

  β-index-suc : ∀ {V Vs i}
    → Value (V ⦂⦂ Vs)
      ------------------------------------------
    → (V ⦂⦂ Vs) ! ($ _ (suc i)) —→  Vs ! ($ _ i)

  β-index-error : ∀ {N}
      -----------------
    → 〈〉 ! N —→ error

  β-let : ∀{V N}
    → Value V
      -------------------
    → `let V N —→ N [ V ]
```

## Multi-step reduction

```
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```

## Canonical Forms

```
data Function : Term → Set where
  Fun-ƛ : ∀ {N} → Function (ƛ N)
  Fun-prim : ∀{b p k} → Function ($ (b ⇒ p) k)
  Fun-error : Function error

canonical-fun : ∀{V A B}
  → ∅ ⊢ V ⦂ A ⇒ B
  → Value V
    ----------
  → Function V
canonical-fun ⊢V V-ƛ = Fun-ƛ
canonical-fun (⊢$ {p = base B-`ℕ} ()) (V-const {_} {k})
canonical-fun (⊢$ {p = base B-Bool} ()) (V-const {_} {k})
canonical-fun (⊢$ {p = b ⇒ p} eq) (V-const {_} {k}) = Fun-prim

data Constant : Base → Term → Set where
  base-const : ∀{b k} → Constant b ($ (base b) k)

canonical-base : ∀{b V A}
  → A ≡ typeof-base b
  → ∅ ⊢ V ⦂ A
  → Value V
    ------------
  → Constant b V
canonical-base {B-`ℕ} () (⊢ƛ ⊢V) V-ƛ
canonical-base {B-Bool} () (⊢ƛ ⊢V) V-ƛ
canonical-base {B-`ℕ} eq (⊢$ {p = base B-`ℕ} refl) V-const = base-const
canonical-base {B-Bool} eq (⊢$ {p = base B-Bool} refl) V-const = base-const
canonical-base {B-`ℕ} refl (⊢$ {p = b' ⇒ p} ()) V-const
canonical-base {B-Bool} refl (⊢$ {p = b' ⇒ p} ()) V-const
canonical-base {B-`ℕ} () (⊢insert ⊢V ⊢V₁) (V-⦂⦂ vV vV₁)
canonical-base {B-Bool} () (⊢insert ⊢V ⊢V₁) (V-⦂⦂ vV vV₁)

data IsArray : Term → Set where
  array-empty : IsArray 〈〉
  array-insert : ∀{V Vs} → IsArray Vs → IsArray (V ⦂⦂ Vs)
 
canonical-array : ∀ {Ms A}
  → ∅ ⊢ Ms ⦂ Array A
  → Value Ms
  → IsArray Ms
canonical-array (⊢$ {p = base B-`ℕ} ()) V-const
canonical-array (⊢$ {p = base B-Bool} ()) V-const
canonical-array ⊢empty V-〈〉 = array-empty
canonical-array (⊢insert ⊢M ⊢Ms) (V-⦂⦂ VM VMs) =
    array-insert (canonical-array ⊢Ms VMs)
```


## Progress

```
data Error : Term → Set where
  is-error : Error error
```

```
data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

  trapped-error :
      Error M
      ----------
    → Progress M
```

```
progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢$ _)                             = done V-const
progress (⊢ƛ ⊢N)                            = done V-ƛ
progress (⊢· {L = L}{M}{A}{B} ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                            = step (ξ (□· M) L—→L′)
... | trapped-error is-error                = step (lift-error (□· M))
... | done VL
        with progress ⊢M
...     | step M—→M′                        = step (ξ ((L ·□) VL) M—→M′)
...     | trapped-error is-error            = step (lift-error ((L ·□) VL))
...     | done VM
            with canonical-fun ⊢L VL
...         | Fun-ƛ                         = step (β-ƛ VM)
...         | Fun-prim {b}{p}{k}
                with ⊢L
...             | ⊢$ refl
                with canonical-base refl ⊢M VM
...             | base-const                = step δ
progress (⊢μ ⊢M)                            = step β-μ
progress (⊢let {N = N} ⊢L ⊢N)
    with progress ⊢L
... | step L—→L′                            = step (ξ (let□ N) L—→L′)
... | trapped-error is-error                = step (lift-error (let□ N))
... | done VL                               = step (β-let VL)
progress ⊢empty                             = done V-〈〉
progress (⊢insert {M = M}{Ms} ⊢M ⊢Ms)
    with progress ⊢M
... | step M—→M′                            = step (ξ (□⦂⦂ Ms) M—→M′)
... | trapped-error is-error                = step (lift-error (□⦂⦂ Ms))
... | done VM
        with progress ⊢Ms
...     | step Ms—→Ms′                      = step (ξ ((M ⦂⦂□) VM) Ms—→Ms′)
...     | trapped-error is-error            = step (lift-error ((M ⦂⦂□) VM))
...     | done VMs                          = done (V-⦂⦂ VM VMs)
progress (⊢! {Ms = M}{N} ⊢M ⊢N)
    with progress ⊢M
... | step M—→M′                            = step (ξ (□! N) M—→M′)
... | trapped-error is-error                = step (lift-error (□! N))
... | done VMs
        with progress ⊢N
...     | step N—→N′                        = step (ξ (M !□) N—→N′)
...     | trapped-error is-error            = step (lift-error (M !□))
...     | done VN
            with canonical-array ⊢M VMs
...         | array-empty                   = step β-index-error
...         | array-insert aVs
            with canonical-base refl ⊢N VN
...         | base-const {b}{0}             = step (β-index-0 VMs)
...         | base-const {b}{suc i}         = step (β-index-suc VMs)
progress ⊢error                             = trapped-error is-error
```

## Renaming and substitution

```
WTRename : Context → Rename → Context → Set
WTRename Γ ρ Δ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ ⦉ ρ ⦊ x ⦂ A
```

```
ext-pres : ∀ {Γ Δ ρ B}
  → WTRename Γ ρ Δ
    --------------------------------
  → WTRename (Γ , B) (ext ρ) (Δ , B)
ext-pres {ρ = ρ } ⊢ρ Z =  Z
ext-pres {ρ = ρ } ⊢ρ (S {x = x} ∋x) =  S (⊢ρ ∋x)
```

```
rename-pres : ∀ {Γ Δ ρ M A}
  → WTRename Γ ρ Δ
  → Γ ⊢ M ⦂ A
    ------------------
  → Δ ⊢ rename ρ M ⦂ A
rename-pres ⊢ρ (⊢` ∋w)            =  ⊢` (⊢ρ ∋w)
rename-pres {ρ = ρ} ⊢ρ (⊢ƛ ⊢N)    =  ⊢ƛ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ⊢ρ) ⊢N)
rename-pres {ρ = ρ} ⊢ρ (⊢· ⊢L ⊢M) =  ⊢· (rename-pres {ρ = ρ} ⊢ρ ⊢L) (rename-pres {ρ = ρ} ⊢ρ ⊢M)
rename-pres {ρ = ρ} ⊢ρ (⊢μ ⊢M)    =  ⊢μ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ⊢ρ) ⊢M)
rename-pres ⊢ρ (⊢$ eq)            = ⊢$ eq
rename-pres {ρ = ρ} ⊢ρ (⊢let ⊢M ⊢N) =
    ⊢let (rename-pres {ρ = ρ} ⊢ρ ⊢M) (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ⊢ρ) ⊢N)
rename-pres ⊢ρ ⊢empty = ⊢empty
rename-pres {ρ = ρ} ⊢ρ (⊢insert ⊢M ⊢Ms) =
    ⊢insert (rename-pres {ρ = ρ} ⊢ρ ⊢M) (rename-pres {ρ = ρ} ⊢ρ ⊢Ms)
rename-pres {ρ = ρ} ⊢ρ (⊢! ⊢Ms ⊢N)       = ⊢! (rename-pres {ρ = ρ} ⊢ρ ⊢Ms) (rename-pres {ρ = ρ} ⊢ρ ⊢N)
rename-pres ⊢ρ ⊢error            = ⊢error
```

```
WTSubst : Context → Subst → Context → Set
WTSubst Γ σ Δ = ∀ {A x} → Γ ∋ x ⦂ A → Δ ⊢ ⟪ σ ⟫ (` x) ⦂ A
```

```
exts-pres : ∀ {Γ Δ σ B}
  → WTSubst Γ σ Δ
    --------------------------------
  → WTSubst (Γ , B) (exts σ) (Δ , B)
exts-pres {σ = σ} Γ⊢σ Z = ⊢` Z
exts-pres {σ = σ} Γ⊢σ (S {x = x} ∋x) = rename-pres {ρ = ↑ 1} S (Γ⊢σ ∋x)
```

```
subst : ∀ {Γ Δ σ N A}
  → WTSubst Γ σ Δ
  → Γ ⊢ N ⦂ A
    ---------------
  → Δ ⊢ ⟪ σ ⟫ N ⦂ A
subst Γ⊢σ (⊢` eq)              = Γ⊢σ eq
subst {σ = σ} Γ⊢σ (⊢ƛ ⊢N)      = ⊢ƛ (subst {σ = exts σ} (exts-pres {σ = σ} Γ⊢σ) ⊢N) 
subst {σ = σ} Γ⊢σ (⊢· ⊢L ⊢M)           = ⊢· (subst {σ = σ} Γ⊢σ ⊢L) (subst {σ = σ} Γ⊢σ ⊢M) 
subst {σ = σ} Γ⊢σ (⊢μ ⊢M)      = ⊢μ (subst {σ = exts σ} (exts-pres {σ = σ} Γ⊢σ) ⊢M) 
subst Γ⊢σ (⊢$ e) = ⊢$ e 
subst {σ = σ} Γ⊢σ (⊢let ⊢M ⊢N) =
    ⊢let (subst {σ = σ} Γ⊢σ ⊢M) (subst {σ = exts σ} (exts-pres {σ = σ} Γ⊢σ) ⊢N) 
subst Γ⊢σ ⊢empty               = ⊢empty
subst {σ = σ} Γ⊢σ (⊢insert ⊢M ⊢Ms)= ⊢insert (subst {σ = σ} Γ⊢σ ⊢M) (subst {σ = σ} Γ⊢σ ⊢Ms) 
subst {σ = σ} Γ⊢σ (⊢! ⊢M ⊢N)   = ⊢! (subst {σ = σ} Γ⊢σ ⊢M) (subst {σ = σ} Γ⊢σ ⊢N) 
subst Γ⊢σ ⊢error               = ⊢error
```

```
substitution : ∀{Γ A B M N}
   → Γ ⊢ M ⦂ A
   → (Γ , A) ⊢ N ⦂ B
     ---------------
   → Γ ⊢ N [ M ] ⦂ B
substitution {Γ}{A}{B}{M}{N} ⊢M ⊢N = subst {σ = M • ↑ 0 } G ⊢N
    where
    G : ∀ {A₁ : Type} {x : ℕ}
      → (Γ , A) ∋ x ⦂ A₁ → Γ ⊢ ⟪ M • ↑ 0 ⟫ (` x) ⦂ A₁
    G {A₁} {zero} Z = ⊢M
    G {A₁} {suc x} (S ∋x) = ⊢` ∋x
```

## Plug Inversion

```
plug-inversion : ∀{M F A}
   → ∅ ⊢ plug M F ⦂ A
     ----------------------------------------------------------------
   → Σ[ B ∈ Type ] ∅ ⊢ M ⦂ B × (∀ M' → ∅ ⊢ M' ⦂ B → ∅ ⊢ plug M' F ⦂ A)
plug-inversion {M} {□· N} {A} (⊢· {A = A'} ⊢M ⊢N) =
    ⟨ A' ⇒ A , ⟨ ⊢M , (λ M' z → ⊢· z ⊢N) ⟩ ⟩
plug-inversion {M} {(L ·□) v} {A} (⊢· {A = A'} ⊢L ⊢M) =
    ⟨ A' , ⟨ ⊢M , (λ M' → ⊢· ⊢L) ⟩ ⟩
plug-inversion {M} {□⦂⦂ Ms} {.(Array _)} (⊢insert {A = A} ⊢M ⊢Ms) =
    ⟨ A , ⟨ ⊢M , (λ M' z → ⊢insert z ⊢Ms) ⟩ ⟩
plug-inversion {M} {(N ⦂⦂□) v} {.(Array _)} (⊢insert {A = A} ⊢N ⊢M) =
    ⟨ Array A , ⟨ ⊢M , (λ M' → ⊢insert ⊢N) ⟩ ⟩
plug-inversion {M} {□! i} {A} (⊢! ⊢M ⊢N) =
    ⟨ (Array A) , ⟨ ⊢M , (λ M' z → ⊢! z ⊢N) ⟩ ⟩
plug-inversion {M} {Ms !□} {A} (⊢! ⊢M ⊢N) =
    ⟨ `ℕ , ⟨ ⊢N , (λ M' → ⊢! ⊢M) ⟩ ⟩
plug-inversion {M} {let□ N} {A} (⊢let {A = A'} ⊢M ⊢N) =
    ⟨ A' , ⟨ ⊢M , (λ M' z → ⊢let z ⊢N) ⟩ ⟩
```

## Preservation

```
preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve ⊢M (ξ {M}{M′} F M—→M′)
    with plug-inversion ⊢M
... | ⟨ B , ⟨ ⊢M' , plug-wt ⟩ ⟩ = plug-wt M′ (preserve ⊢M' M—→M′)
preserve ⊢M (lift-error F) = ⊢error
preserve (⊢· (⊢ƛ ⊢N) ⊢M) (β-ƛ vV) = substitution ⊢M ⊢N
preserve (⊢μ ⊢M) β-μ = substitution (⊢μ ⊢M) ⊢M
preserve (⊢· (⊢$ refl) (⊢$ refl)) δ = ⊢$ refl
preserve (⊢! (⊢insert ⊢M ⊢Ms) ⊢N) (β-index-0 vMMs) = ⊢M
preserve (⊢! (⊢insert ⊢M ⊢Ms) ⊢N) (β-index-suc vVVs) = ⊢! ⊢Ms (⊢$ refl)
preserve ⊢M β-index-error = ⊢error
preserve (⊢let ⊢M ⊢N) (β-let vV) = substitution ⊢M ⊢N
```
