```
open import Relation.Binary.PropositionalEquality
                         using    (_≡_; refl; cong; cong₂)
open import Function     using    (case_of_)
open import Data.Product using    (∃-syntax; _×_; proj₁; proj₂)
                         renaming (_,_ to ⟨_,_⟩)


-- | We start with the intrinsically-typed STLC from the
-- |   "DeBruijn" lecture but with `let` added.
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  9 `_
infix  5 ƛ_
infixl 7 _·_

data Type : Set where
  `ℕ     : Type
  _⇒_   : Type → Type → Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B

data _⊢_ : Context → Type → Set where

  `zero : ∀ {Γ}
      ------
    → Γ ⊢ `ℕ

  `_ : ∀ {Γ A}
    → Γ ∋ A
      ---------
    → Γ ⊢ A

  ƛ_  :  ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------------
    → Γ ⊢ B

  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ---------------
    → Γ ⊢ B

_→ʳ_ : Context → Context → Set
Γ →ʳ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

ext : ∀ {Γ Δ A}
  → Γ →ʳ Δ
    ---------------------------------
  → (Γ , A) →ʳ (Δ , A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ A}
  → (ρ : Γ →ʳ Δ)
  → Γ ⊢ A
    ------------------
  → Δ ⊢ A
rename ρ (`zero)        =  `zero
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`let M N)     =  `let (rename ρ M) (rename (ext ρ) N)

⇑_ : ∀ {Γ A B} → Γ ⊢ A → Γ , B ⊢ A
⇑ M = rename S_ M

_→ˢ_ : Context → Context → Set
Γ →ˢ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

exts : ∀ {Γ Δ A}
  → Γ →ˢ Δ
    ---------------------------
  → (Γ , A) →ˢ (Δ , A)
exts σ Z      =  ` Z
exts σ (S x)  =  ⇑ σ x

subst : ∀ {Γ Δ A}
  → (σ : Γ →ˢ Δ)
  → Γ ⊢ A
    ---------------
  → Δ ⊢ A
subst σ `zero = `zero
subst σ (` x) = σ x
subst σ (ƛ M) = ƛ subst (exts σ) M
subst σ (M · N) = subst σ M · subst σ N
subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)

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

data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-zero : ∀ {Γ}
      ---------------------
    → Value (`zero {Γ})

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ------------------------------
    → Value (ƛ N)


infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ------------------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ------------------------
    → V · M —→ V · M′

  ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
    → M —→ M′
      ------------------------------
    → `let M N —→ `let M′ N

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
    → Value V
      ------------------------------
    → (ƛ N) · V —→ N [ V ]

  β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
    → Value V
      ------------------------------
    → `let V N —→ N [ V ]

```

Some constructs can be defined in terms of other constructs.
We look at how to formalise this notion.

We define *simulation* between two systems with different terms
and reduction rules. Let's call them source (M, N) and target (M†, N†).
We define a relation M ~ M† between corresponding terms of the two systems.

Simulation: for every M, M†, and N,
if M ~ M† and M —→ N
then M† —↠ N† and N ~ N† for some N†.

M   —→   N
|          |
~          ~
|          |
M†  —↠  N†
(note the multi-step reduction)

Sometimes we will have a stronger condition
called *lock-step simulation*:

M   —→   N
|          |
~          ~
|          |
M†  —→  N†
(note the single-step reduction in the target)

If ~ is a simulation from source to target, and
the converse of ~ is a simulation from target to source,
this situation is called a *bisimulation*, which we're
particularly interested in.

In the following example, we use lambda calculus with let added
as the source, and the same system with let translated out as the target:

```

infix 0 _†

_† : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
`zero    †  = `zero
` x      †  = ` x
ƛ N      †  = ƛ (N †)
L · M    †  = (L †) · (M †)
`let M N †  = (ƛ (N †)) · (M †)
```

We define the simulation relation M ~ M† between source and target:

```

infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

data _~_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where

  ~zero : ∀ {Γ}
     ---------------------
   → `zero ~ `zero {Γ}

  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------------------
   → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ---------------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ------------------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ---------------------------
    → `let M N ~ ((ƛ N†) · M†)    -- !!
```

We now show that M † ≡ N implies M ~ N, and conversely.

```
†-impl-~ : ∀ {Γ A} {M N : Γ ⊢ A} → (M †) ≡ N → M ~ N
†-impl-~ M†=N = {!!}

~-impl-† : ∀ {Γ A} {M N : Γ ⊢ A} → M ~ N → (M †) ≡ N
~-impl-† M~N = {!!}
```

Simulation commutes with values:
if M ~ M† and M is a value then M† is also a value.

```
~val : ∀ {Γ A} {V V† : Γ ⊢ A}
  → V ~ V†
  → Value V
    ------------
  → Value V†
~val ~zero   V-zero = V-zero
~val (~ƛ _)  V-ƛ    = V-ƛ
```

The other direction is also true:

```
~val⁻¹ : ∀ {Γ A} {V V† : Γ ⊢ A}
  → V ~ V†
  → Value V†
    ------------
  → Value V
~val⁻¹ ~zero   V-zero = V-zero
~val⁻¹ (~ƛ _)  V-ƛ    = V-ƛ
```

Simulation commutes with renaming: if ρ maps any judgment Γ ∋ A to a judgment Δ ∋ A,
and if M ~ M† then rename ρ M ~ rename ρ M†.

```
~rename : ∀ {Γ Δ A} {M M† : Γ ⊢ A}
  → (ρ : Γ →ʳ Δ)
  → M ~ M†
    ------------------------------
  → rename ρ M ~ rename ρ M†
~rename ρ M~M† = {!!}
```

Simulation commutes with substitution: If σ and σ† both map any judgment Γ ∋ A to
a judgment Δ ⊢ A, such that for every x in Γ ∋ A we have σ x ~ σ† x,
and if M ~ M†, then subst σ M ~ subst σ† M†.

```
infix 4 _∼_

_∼_ : ∀ {Γ Δ} → (σ σ† : Γ →ˢ Δ) → Set
_∼_ {Γ} {Δ} σ σ† = ∀ {A} (x : Γ ∋ A) → σ x ~ σ† x

~exts : ∀ {Γ Δ A} {σ σ† : Γ →ˢ Δ}
  → σ ∼ σ†
    ------------------------------------
  → _∼_ {Γ , A} (exts σ) (exts σ†)
~exts σ~σ† = {!!}

~subst : ∀ {Γ Δ A} {σ σ† : Γ →ˢ Δ} {M M† : Γ ⊢ A}
  → σ ∼ σ†
  → M ~ M†
    ------------------------------
  → subst σ M ~ subst σ† M†
~subst σ~σ† M~M† = {!!}

~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
  → N ~ N†
  → M ~ M†
    ------------------------
  → N [ M ] ~ N† [ M† ]
~sub {Γ} {A} {B} N~N† M~M† = ~subst ~σ₀ N~N†
  where
  ~σ₀ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
  ~σ₀ Z      =  M~M†
  ~σ₀ (S x)  =  ~`

data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

  leg : ∀ {N† : Γ ⊢ A}
    → N ~ N†
    → M† —→ N†
      ---------------
    → Leg M† N

{- For each reduction step in the source,
   we must show a corresponding reduction in the target. -}
sim : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ M†
  → M —→ N
    ------------
  → Leg M† N
sim M~M† M→N = {!!}

data Leg⁻¹ {Γ A} (M N† : Γ ⊢ A) : Set where

  leg : ∀ {N : Γ ⊢ A}
    → N ~ N†
    → M —→ N
      ---------------
    → Leg⁻¹ M N†

sim⁻¹ : ∀ {Γ A} {M M† N† : Γ ⊢ A}
  → M ~ M†
  → M† —→ N†
    ---------------
  → Leg⁻¹ M N†
sim⁻¹ (L~L† ~· M~M†) (ξ-·₁ L†→L†′) =
  case sim⁻¹ L~L† L†→L†′ of λ where
  (leg L′~L†′ L→L′) → leg (L′~L†′ ~· M~M†) (ξ-·₁ L→L′)
sim⁻¹ (L~L† ~· M~M†) (ξ-·₂ vL† M†→M†′) =
  case sim⁻¹ M~M† M†→M†′ of λ where
  (leg M′~M†′ M→M′) → leg (L~L† ~· M′~M†′) (ξ-·₂ (~val⁻¹ L~L† vL†) M→M′)
sim⁻¹ ((~ƛ N~N†) ~· M~M†) (β-ƛ vM†) =
  leg (~sub N~N† M~M†) (β-ƛ (~val⁻¹ M~M† vM†))
sim⁻¹ (~let M~M† N~N†) (ξ-·₂ vλN† M†→M†′) =
  case sim⁻¹ M~M† M†→M†′ of λ where
  (leg M′~M†′ M→M′) → leg (~let M′~M†′ N~N†) (ξ-let M→M′)
sim⁻¹ (~let M~M† N~N†) (β-ƛ vM†) =
  leg (~sub N~N† M~M†) (β-let (~val⁻¹ M~M† vM†))
```

(Alternatively, we could use an existential instead of the Leg datatype.)

```
-- if M ~ M† and M† —→ N† then M —→ N and N ~ N† for some N
sim⁻¹′ : ∀ {Γ A} {M M† N† : Γ ⊢ A}
  → M ~ M†
  → M† —→ N†
    ------------------------------
  → ∃[ N ] N ~ N† × (M —→ N)
sim⁻¹′ {M = L · M} (L~L† ~· M~M†) (ξ-·₁ L†→L†′) =
  case sim⁻¹′ L~L† L†→L†′ of λ where
  ⟨ L′ , ⟨ L′~L†′ , L→L′ ⟩ ⟩ →
    ⟨ L′ · M , ⟨ L′~L†′ ~· M~M† , ξ-·₁ L→L′ ⟩ ⟩
sim⁻¹′ {M = L · M} (L~L† ~· M~M†) (ξ-·₂ vL† M†→M†′) =
  case sim⁻¹′ M~M† M†→M†′ of λ where
  ⟨ M′ , ⟨ M′~M†′ , M→M′ ⟩ ⟩ →
    ⟨ L · M′ , ⟨ L~L† ~· M′~M†′ , ξ-·₂ (~val⁻¹ L~L† vL†) M→M′ ⟩ ⟩
sim⁻¹′ {M = (ƛ N) · M} ((~ƛ N~N†) ~· M~M†) (β-ƛ vM†) =
  ⟨ N [ M ] , ⟨ (~sub N~N† M~M†) , (β-ƛ (~val⁻¹ M~M† vM†)) ⟩ ⟩
sim⁻¹′ {M = `let M N} (~let M~M† N~N†) (ξ-·₂ vλN† M†→M†′) =
  case sim⁻¹′ M~M† M†→M†′ of λ where
  ⟨ M′ , ⟨ M′~M†′ , M→M′ ⟩ ⟩ → ⟨ `let M′ N , ⟨ ~let M′~M†′ N~N† , ξ-let M→M′ ⟩ ⟩
sim⁻¹′ {M = `let M N} (~let M~M† N~N†) (β-ƛ vM†) =
  ⟨ N [ M ] , ⟨ ~sub N~N† M~M† , β-let (~val⁻¹ M~M† vM†) ⟩ ⟩
```
