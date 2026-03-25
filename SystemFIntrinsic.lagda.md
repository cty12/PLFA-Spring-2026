```
{-# OPTIONS --rewriting #-}

module SystemFIntrinsic where

-- Need the following two imports for rewriting
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)
open import Level using (0ℓ; Lift; lift) renaming (suc to lsuc)
open import Function using (case_of_)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      ---------------------------
    → f ≡ g
```

(Quoting from TAPL)
Abstraction principle: Each significant piece of functionality in a
program should be implemented in just one place in the source code.
Where similar functions are carried out by distinct pieces of code, it
is generally beneficial to combine them into one by abstracting out the
varying parts.

For example,

cons-int  : Int -> List Int -> List Int
cons-bool : Bool -> List Bool -> List Bool

Only types vary. We abstract out a type from a term:

cons : ∀α. α -> List α -> List α

We can then instantiate this abstract term with concrete types.

(Quoting from TAPL again)
Type systems that allow a single piece of code to be used with multiple types
are collectively known as polymorphic systems (poly = many, morph = form).

In this lecture we focus on parametric polymorphism, which allows
a single piece of code to be typed “generically,” using variables
in place of actual types, and then instantiated with particular types
as needed.

System F: STLC with universal types

types      A ::= ... | α | ∀α. A
terms      M ::= ... | Λα. M | M [ A ]  (in the Agda code below, we use _∙_ for type application)

```

infixr 7 _⇒_
infixr 6 _•ᵗ_
infixl 5 _,_
infix  4 _∋_
infix  4 _;_⊢_

infix  9 `_
infix  5 ƛ_˙_
infixl 7 _·_
infixl 7 _∙_
infix  8 `suc_

infix  2 _—→_
```

Type environment   Δ ::= ∅ | Δ , α

We use De Bruijn indices to represent type variables.
The type environment is isomorphic to a Nat.

```
---------------------------------------------------
-- | Type variable contexts and type variables | --
---------------------------------------------------

infixl 5 _,α

data TyCtx : Set where
  ∅    : TyCtx
  _,α  : TyCtx → TyCtx

data TyVar : (Δ : TyCtx) → Set where
  Z  : ∀ {Δ} → TyVar (Δ ,α)
  S_ : ∀ {Δ} → TyVar Δ → TyVar (Δ ,α)

```

We now define well-formed types: Δ ⊢ A
Again, we use the intrinsically-typed notation (A : Type Δ) in Agda.

```

---------------
-- | Types | --
---------------

data Type : TyCtx → Set where
  `_     : ∀ {Δ} → TyVar Δ → Type Δ
  `Nat   : ∀ {Δ} → Type Δ
  `Bool  : ∀ {Δ} → Type Δ
  _⇒_   : ∀ {Δ} → Type Δ → Type Δ → Type Δ
  `∀_    : ∀ {Δ} → Type (Δ ,α) → Type Δ

------------------------------------
-- | Substitute types into type | --
------------------------------------

infixr 7 _⇒ʳ_

_⇒ʳ_ : TyCtx → TyCtx → Set
Δ ⇒ʳ Δ' = TyVar Δ → TyVar Δ'

extᵗ : ∀ {Δ Δ'} → Δ ⇒ʳ Δ' → (Δ ,α) ⇒ʳ (Δ' ,α)
extᵗ ρ Z      = Z
extᵗ ρ (S x)  = S (ρ x)

renameᵗ : ∀ {Δ Δ'} → Δ ⇒ʳ Δ' → Type Δ → Type Δ'
renameᵗ ρ (` x)   = ` (ρ x)
renameᵗ ρ `Nat     = `Nat
renameᵗ ρ `Bool    = `Bool
renameᵗ ρ (A ⇒ B)  = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A)  = `∀ (renameᵗ (extᵗ ρ) A)

renameᵗ-cong : ∀ {Δ Δ'} {ρ ρ' : Δ ⇒ʳ Δ'} (A : Type Δ)
  → (∀ α → ρ α ≡ ρ' α)
    ---------------------------------
  → renameᵗ ρ A ≡ renameᵗ ρ' A
renameᵗ-cong (` α) eq = cong `_ (eq α)
renameᵗ-cong `Nat _ = refl
renameᵗ-cong `Bool _ = refl
renameᵗ-cong (A ⇒ B) eq rewrite renameᵗ-cong A eq | renameᵗ-cong B eq = refl
renameᵗ-cong {ρ = ρ} {ρ'} (`∀ A) eq = cong `∀_ (renameᵗ-cong A ext-eq)
  where
  ext-eq : ∀ α → extᵗ ρ α ≡ extᵗ ρ' α
  ext-eq Z      = refl
  ext-eq (S α)  = cong S_ (eq α)

renameᵗ-comp : ∀ {Δ₁ Δ₂ Δ₃} (ρ₁ : Δ₁ ⇒ʳ Δ₂) (ρ₂ : Δ₂ ⇒ʳ Δ₃) A
    ---------------------------------------------------------------
  → renameᵗ ρ₂ (renameᵗ ρ₁ A) ≡ renameᵗ (λ α → ρ₂ (ρ₁ α)) A
renameᵗ-comp ρ₁ ρ₂ (` α)  = refl
renameᵗ-comp ρ₁ ρ₂ `Nat   = refl
renameᵗ-comp ρ₁ ρ₂ `Bool  = refl
renameᵗ-comp ρ₁ ρ₂ (A ⇒ B)
  rewrite renameᵗ-comp ρ₁ ρ₂ A | renameᵗ-comp ρ₁ ρ₂ B = refl
renameᵗ-comp ρ₁ ρ₂ (`∀ A) = cong `∀_
    (trans (renameᵗ-comp (extᵗ ρ₁) (extᵗ ρ₂) A)
           (renameᵗ-cong A ext-comp))
  where
  ext-comp : ∀ α → extᵗ ρ₂ (extᵗ ρ₁ α) ≡ extᵗ (λ β → ρ₂ (ρ₁ β)) α
  ext-comp Z      = refl
  ext-comp (S α)  = refl
{-# REWRITE renameᵗ-comp #-}

⇑ᵗ : ∀ {Δ} (A : Type Δ) → Type (Δ ,α)
⇑ᵗ = renameᵗ S_

-- check
renameᵗ-shift : ∀ {Δ Ξ} (ρ : Δ ⇒ʳ Ξ) A → renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
renameᵗ-shift ρ A = refl

infixr 7 _⇒ˢ_

_⇒ˢ_ : TyCtx → TyCtx → Set
Δ ⇒ˢ Δ' = TyVar Δ → Type Δ'

idᵗ : ∀ {Δ} → Δ ⇒ˢ Δ
idᵗ = `_

↑ᵗ : ∀ {Δ} → Δ ⇒ˢ (Δ ,α)
↑ᵗ α = ` (S α)

extsᵗ : ∀ {Δ Δ'} → Δ ⇒ˢ Δ' → (Δ ,α) ⇒ˢ (Δ' ,α)
extsᵗ σ Z      = ` Z
extsᵗ σ (S x)  = ⇑ᵗ (σ x)

_•ᵗ_ : ∀ {Δ Δ'} → Type Δ' → Δ ⇒ˢ Δ' → (Δ ,α) ⇒ˢ Δ'
(A •ᵗ σ) Z      = A
(A •ᵗ σ) (S α)  = σ α

substᵗ : ∀ {Δ Δ'} → Δ ⇒ˢ Δ' → Type Δ → Type Δ'
substᵗ σ (` x)   = σ x
substᵗ σ `Nat     = `Nat
substᵗ σ `Bool    = `Bool
substᵗ σ (A ⇒ B)  = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (`∀ A)  = `∀ (substᵗ (extsᵗ σ) A)

infixr 5 _⨟ᵗ_

_⨟ᵗ_ : ∀ {Δ₁ Δ₂ Δ₃} → Δ₁ ⇒ˢ Δ₂ → Δ₂ ⇒ˢ Δ₃ → Δ₁ ⇒ˢ Δ₃
(σ ⨟ᵗ τ) α = substᵗ τ (σ α)

σ₀ᵗ : ∀ {Δ} → Type Δ → (Δ ,α) ⇒ˢ Δ
σ₀ᵗ B = B •ᵗ idᵗ

_[_]ᵗ : ∀ {Δ} → Type (Δ ,α) → Type Δ → Type Δ
A [ B ]ᵗ = substᵗ (σ₀ᵗ B) A

substᵗ-cong : ∀ {Δ Δ'} {σ τ : Δ ⇒ˢ Δ'} A
  → (∀ α → σ α ≡ τ α)
    ------------------------------
  → substᵗ σ A ≡ substᵗ τ A
substᵗ-cong (` α) eq = eq α
substᵗ-cong `Nat _ = refl
substᵗ-cong `Bool _ = refl
substᵗ-cong (A ⇒ B) eq rewrite substᵗ-cong A eq | substᵗ-cong B eq = refl
substᵗ-cong {σ = σ} {τ} (`∀ A) eq = cong `∀_ (substᵗ-cong A exts-eq)
  where
  exts-eq : ∀ α → extsᵗ σ α ≡ extsᵗ τ α
  exts-eq Z      = refl
  exts-eq (S α)  = cong ⇑ᵗ (eq α)

extsᵗ-extᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₁ ⇒ʳ Δ₂) (σ : Δ₂ ⇒ˢ Δ₃) α
      ------------------------------------------------------------
    → extsᵗ σ (extᵗ ρ α) ≡ extsᵗ (λ β → σ (ρ β)) α
extsᵗ-extᵗ ρ σ Z      = refl
extsᵗ-extᵗ ρ σ (S _)  = refl
{-# REWRITE extsᵗ-extᵗ #-}

ren-subᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₁ ⇒ʳ Δ₂) (σ : Δ₂ ⇒ˢ Δ₃) A
      ---------------------------------------------------------------
    → substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ α → σ (ρ α)) A
ren-subᵗ ρ σ (` α)  = refl
ren-subᵗ ρ σ `Nat   = refl
ren-subᵗ ρ σ `Bool  = refl
ren-subᵗ ρ σ (A ⇒ B) rewrite ren-subᵗ ρ σ A | ren-subᵗ ρ σ B = refl
ren-subᵗ ρ σ (`∀ A)   rewrite ren-subᵗ (extᵗ ρ) (extsᵗ σ) A = refl
{-# REWRITE ren-subᵗ #-}

sub-idᵗ : ∀ {Δ} (A : Type Δ) → substᵗ idᵗ A ≡ A
sub-idᵗ (` x)    = refl
sub-idᵗ `Nat     = refl
sub-idᵗ `Bool    = refl
sub-idᵗ (A ⇒ B)  rewrite sub-idᵗ A | sub-idᵗ B = refl
sub-idᵗ (`∀ A) = cong `∀_ eq
    where
    exts-id : ∀ α → extsᵗ idᵗ α ≡ ` α
    exts-id Z      = refl
    exts-id (S _)  = refl
    eq : substᵗ (extsᵗ idᵗ) A ≡ A
    eq rewrite substᵗ-cong A exts-id | sub-idᵗ A = refl
{-# REWRITE sub-idᵗ #-}

σ₀ᵗ-extᵗ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') (B : Type Δ) (x : TyVar (Δ ,α))
    → renameᵗ ρ (σ₀ᵗ B x) ≡ σ₀ᵗ (renameᵗ ρ B) (extᵗ ρ x)
σ₀ᵗ-extᵗ ρ B Z      = refl
σ₀ᵗ-extᵗ ρ B (S x)  = refl
{-# REWRITE σ₀ᵗ-extᵗ #-}

extᵗ-extsᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₂ ⇒ʳ Δ₃) (σ : Δ₁ ⇒ˢ Δ₂) α
      ------------------------------------------------------------------
    → renameᵗ (extᵗ ρ) (extsᵗ σ α) ≡ extsᵗ (λ β → renameᵗ ρ (σ β)) α
extᵗ-extsᵗ ρ σ Z     = refl
extᵗ-extsᵗ ρ σ (S α) = refl
{-# REWRITE extᵗ-extsᵗ #-}

sub-renᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₂ ⇒ʳ Δ₃) (σ : Δ₁ ⇒ˢ Δ₂) A
      ---------------------------------------------------------------
    → renameᵗ ρ (substᵗ σ A) ≡ substᵗ (λ α → renameᵗ ρ (σ α)) A
sub-renᵗ ρ σ (` α)  = refl
sub-renᵗ ρ σ `Nat   = refl
sub-renᵗ ρ σ `Bool  = refl
sub-renᵗ ρ σ (A ⇒ B) rewrite sub-renᵗ ρ σ A | sub-renᵗ ρ σ B = refl
sub-renᵗ ρ σ (`∀ A) rewrite sub-renᵗ (extᵗ ρ) (extsᵗ σ) A = refl
{-# REWRITE sub-renᵗ #-}

-- check
renameᵗ-[]ᵗ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') (A : Type (Δ ,α)) (B : Type Δ)
    → renameᵗ ρ (A [ B ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ renameᵗ ρ B ]ᵗ
renameᵗ-[]ᵗ ρ A B = refl

extsᵗ-substᵗ : ∀ {Δ₁ Δ₂ Δ₃} (σ : Δ₁ ⇒ˢ Δ₂) (τ : Δ₂ ⇒ˢ Δ₃) α
      ------------------------------------------------------------
    → substᵗ (extsᵗ τ) (extsᵗ σ α) ≡ extsᵗ (σ ⨟ᵗ τ) α
extsᵗ-substᵗ σ τ Z      = refl
extsᵗ-substᵗ σ τ (S x) = refl
{-# REWRITE extsᵗ-substᵗ #-}

sub-subᵗ : ∀ {Δ₁ Δ₂ Δ₃} (σ : Δ₁ ⇒ˢ Δ₂) (τ : Δ₂ ⇒ˢ Δ₃) A
      ---------------------------------------------------------------
    → substᵗ τ (substᵗ σ A) ≡ substᵗ (σ ⨟ᵗ τ) A
sub-subᵗ σ τ (` α)   = refl
sub-subᵗ σ τ `Nat    = refl
sub-subᵗ σ τ `Bool   = refl
sub-subᵗ σ τ (A ⇒ B) rewrite sub-subᵗ σ τ A | sub-subᵗ σ τ B = refl
sub-subᵗ σ τ (`∀ A) rewrite sub-subᵗ (extsᵗ σ) (extsᵗ τ) A = refl
{-# REWRITE sub-subᵗ #-}

substᵗ-σ₀ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') (B : Type Δ) (x : TyVar (Δ ,α))
    → substᵗ σ (σ₀ᵗ B x) ≡ substᵗ (σ₀ᵗ (substᵗ σ B)) (extsᵗ σ x)
substᵗ-σ₀ σ B Z      = refl
substᵗ-σ₀ σ B (S x)  = refl
{-# REWRITE substᵗ-σ₀ #-}

substᵗ-[]ᵗ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') (A : Type (Δ ,α)) (B : Type Δ)
    → substᵗ σ (A [ B ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ substᵗ σ B ]ᵗ
substᵗ-[]ᵗ σ A B rewrite sym (sub-subᵗ (extsᵗ σ) (σ₀ᵗ (substᵗ σ B)) A) = refl

-- | Needed for type preservation for System F
exts-sub-consᵗ : ∀ {Δ Δ'} (A : Type (Δ ,α)) (σ : Δ ⇒ˢ Δ') (B : Type Δ')
    -- (substᵗ (extsᵗ σ) A) [ B ]ᵗ ≡ substᵗ (B •ᵗ σ) A
    → substᵗ (extsᵗ σ ⨟ᵗ B •ᵗ idᵗ) A ≡ substᵗ (B •ᵗ σ) A
exts-sub-consᵗ A σ B = trans (sub-subᵗ (extsᵗ σ) (σ₀ᵗ B) A) (substᵗ-cong A eq)
    where
    eq : ∀ β → substᵗ (σ₀ᵗ B) (extsᵗ σ β) ≡ (B •ᵗ σ) β
    eq Z      = refl
    eq (S β)  = refl
{-# REWRITE exts-sub-consᵗ #-}

```

We also need a notion of well-typed typing contexts: Δ ⊢ Γ

```
------------------------------------------
-- | Term contexts and term variables | --
------------------------------------------

data Ctx (Δ : TyCtx) : Set where
  ∅   : Ctx Δ
  _,_ : Ctx Δ → Type Δ → Ctx Δ

data _∋_ {Δ : TyCtx} : Ctx Δ → Type Δ → Set where
  Z  : ∀ {Γ A} → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A


renameCtx : ∀ {Δ Δ'} → Δ ⇒ʳ Δ' → Ctx Δ → Ctx Δ'
renameCtx ρ ∅       = ∅
renameCtx ρ (Γ , A)  = renameCtx ρ Γ , renameᵗ ρ A

substCtx : ∀ {Δ Δ'} → Δ ⇒ˢ Δ' → Ctx Δ → Ctx Δ'
substCtx σ ∅       = ∅
substCtx σ (Γ , A) = substCtx σ Γ , substᵗ σ A

renameᵗ-∋ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') {Γ : Ctx Δ} {A : Type Δ}
  → Γ ∋ A
  → renameCtx ρ Γ ∋ renameᵗ ρ A
renameᵗ-∋ ρ Z      = Z
renameᵗ-∋ ρ (S x)  = S (renameᵗ-∋ ρ x)

substᵗ-∋ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') {Γ : Ctx Δ} {A : Type Δ}
  → Γ ∋ A
  → substCtx σ Γ ∋ substᵗ σ A
substᵗ-∋ σ Z      = Z
substᵗ-∋ σ (S x)  = S (substᵗ-∋ σ x)

⇑ᶜ : ∀ {Δ} → Ctx Δ → Ctx (Δ ,α)
⇑ᶜ = renameCtx S_

```

The typing judgement takes the form Δ ; Γ ⊢ M : A

```

-----------------------------------
-- | Intrinsically typed terms | --
-----------------------------------

data _;_⊢_ (Δ : TyCtx) (Γ : Ctx Δ) : Type Δ → Set where

  `true :
      --------------- (T-True)
    Δ ; Γ ⊢ `Bool

  `false :
      ---------------- (T-False)
    Δ ; Γ ⊢ `Bool

  `zero :
      --------------- (T-Zero)
    Δ ; Γ ⊢ `Nat

  `suc_ :
    Δ ; Γ ⊢ `Nat
      ----------------- (T-Suc)
    → Δ ; Γ ⊢ `Nat

  `case-nat : ∀ {A}
    → Δ ; Γ ⊢ `Nat
    → Δ ; Γ ⊢ A
    → Δ ; Γ , `Nat ⊢ A
      ---------------------- (T-CaseNat)
    → Δ ; Γ ⊢ A

  `if_then_else : ∀ {A}
    → Δ ; Γ ⊢ `Bool
    → Δ ; Γ ⊢ A
    → Δ ; Γ ⊢ A
      ---------------------- (T-If)
    → Δ ; Γ ⊢ A

  `_ : ∀ {A}
    → Γ ∋ A
      --------------- (T-Var)
    → Δ ; Γ ⊢ A

  ƛ_˙_ : ∀ {B}
    → (A : Type Δ)
    → Δ ; Γ , A ⊢ B
      ------------------ (T-Abs)
    → Δ ; Γ ⊢ A ⇒ B

  _·_ : ∀ {A B}
    → Δ ; Γ ⊢ A ⇒ B
    → Δ ; Γ ⊢ A
      ------------------ (T-App)
    → Δ ; Γ ⊢ B

  -- | New rules for System F | --
  Λ_ : ∀ {A}
    → Δ ,α ; ⇑ᶜ Γ ⊢ A
      --------------------- (T-TAbs)
    → Δ ; Γ ⊢ `∀ A

  _∙_    : ∀ {A : Type (Δ ,α)}
    → Δ ; Γ ⊢ (`∀ A)
    → (B : Type Δ)
      --------------------- (T-TApp)
    → Δ ; Γ ⊢ A [ B ]ᵗ


------------------------------------
-- | Substitute types into term | --
------------------------------------

renameCtx-extᵗ-⇑ᶜ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') (Γ : Ctx Δ)
  → renameCtx (extᵗ ρ) (⇑ᶜ Γ) ≡ ⇑ᶜ (renameCtx ρ Γ)
renameCtx-extᵗ-⇑ᶜ ρ ∅ = refl
renameCtx-extᵗ-⇑ᶜ ρ (Γ , A) rewrite renameCtx-extᵗ-⇑ᶜ ρ Γ = refl

renameᵀ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') {Γ : Ctx Δ} {A : Type Δ}
  → Δ ; Γ ⊢ A
  → Δ' ; renameCtx ρ Γ ⊢ renameᵗ ρ A
renameᵀ ρ `zero         = `zero
renameᵀ ρ `true         = `true
renameᵀ ρ `false        = `false
renameᵀ ρ (`suc M)      = `suc (renameᵀ ρ M)
renameᵀ ρ (`case-nat L M N) = `case-nat (renameᵀ ρ L) (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (`if_then_else L M N) = `if_then_else (renameᵀ ρ L) (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (` x)         = ` (renameᵗ-∋ ρ x)
renameᵀ ρ (ƛ A ˙ N)     = ƛ renameᵗ ρ A ˙ (renameᵀ ρ N)
renameᵀ ρ (L · M)       = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ (Λ N)         = Λ (substEq (_ ;_⊢ _) (renameCtx-extᵗ-⇑ᶜ ρ _) (renameᵀ (extᵗ ρ) N))
renameᵀ ρ (M ∙ A)       = renameᵀ ρ M ∙ renameᵗ ρ A

substCtx-extsᵗ-⇑ᶜ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') (Γ : Ctx Δ)
  → substCtx (extsᵗ σ) (⇑ᶜ Γ) ≡ ⇑ᶜ (substCtx σ Γ)
substCtx-extsᵗ-⇑ᶜ σ ∅ = refl
substCtx-extsᵗ-⇑ᶜ σ (Γ , A) rewrite substCtx-extsᵗ-⇑ᶜ σ Γ = refl
{-# REWRITE substCtx-extsᵗ-⇑ᶜ #-}

substᵀ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') {Γ : Ctx Δ} {A : Type Δ}
  → Δ ; Γ ⊢ A
  → Δ' ; substCtx σ Γ ⊢ substᵗ σ A
substᵀ σ `zero             = `zero
substᵀ σ `true             = `true
substᵀ σ `false            = `false
substᵀ σ (`suc M)          = `suc (substᵀ σ M)
substᵀ σ (`case-nat L M N) = `case-nat (substᵀ σ L) (substᵀ σ M) (substᵀ σ N)
substᵀ σ (`if_then_else L M N) = `if_then_else (substᵀ σ L) (substᵀ σ M) (substᵀ σ N)
substᵀ σ (` x)             = ` (substᵗ-∋ σ x)
substᵀ σ (ƛ A ˙ N)         = ƛ substᵗ σ A ˙ (substᵀ σ N)
substᵀ σ (L · M)           = substᵀ σ L · substᵀ σ M
substᵀ σ (Λ N)             = Λ (substᵀ (extsᵗ σ) N)
substᵀ σ (M ∙ A)           = substᵀ σ M ∙ substᵗ σ A

substCtx-σ₀-⇑ᶜ-cancel : ∀ {Δ} (Γ : Ctx Δ) (B : Type Δ)
  → substCtx (σ₀ᵗ B) (⇑ᶜ Γ) ≡ Γ
substCtx-σ₀-⇑ᶜ-cancel ∅ B = refl
substCtx-σ₀-⇑ᶜ-cancel (Γ , A) B rewrite substCtx-σ₀-⇑ᶜ-cancel Γ B = refl
{-# REWRITE substCtx-σ₀-⇑ᶜ-cancel #-}

_[_]ᵀ : ∀ {Δ} {Γ : Ctx Δ} {A : Type (Δ ,α)}
  → Δ ,α ; ⇑ᶜ Γ ⊢ A
  → (B : Type Δ)
    ---------------------------
  → Δ ; Γ ⊢ A [ B ]ᵗ
_[_]ᵀ N B = substᵀ (σ₀ᵗ B) N


------------------------------------
-- | Substitute terms into term | --
------------------------------------

_→ʳ_ : ∀ {Δ} → Ctx Δ → Ctx Δ → Set
_→ʳ_ Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

idʳ : ∀ {Δ} {Γ : Ctx Δ} → Γ →ʳ Γ
idʳ x = x

ext : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  → Γ →ʳ Γ'
  → (Γ , A) →ʳ (Γ' , A)
ext ρ Z      = Z
ext ρ (S x)  = S (ρ x)

⇑ʳ : ∀ {Δ} {Γ Γ' : Ctx Δ}
  → Γ →ʳ Γ'
  → (⇑ᶜ Γ) →ʳ (⇑ᶜ Γ')
⇑ʳ {Γ = ∅}     ρ ()
⇑ʳ {Γ = Γ , A} ρ Z      = renameᵗ-∋ S_ (ρ Z)
⇑ʳ {Γ = Γ , A} ρ (S x)  = ⇑ʳ (λ y → ρ (S y)) x

rename : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  → Γ →ʳ Γ'
  → Δ ; Γ ⊢ A
  → Δ ; Γ' ⊢ A
rename ρ `zero        = `zero
rename ρ `true        = `true
rename ρ `false       = `false
rename ρ (`suc M)     = `suc (rename ρ M)
rename ρ (`case-nat L M N) = `case-nat (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (`if_then_else L M N) = `if_then_else (rename ρ L) (rename ρ M) (rename ρ N)
rename ρ (` x)        = ` (ρ x)
rename ρ (ƛ _ ˙ N)    = ƛ _ ˙ (rename (ext ρ) N)
rename ρ (L · M)      = rename ρ L · rename ρ M
rename ρ (Λ N)        = Λ (rename (⇑ʳ ρ) N)
rename ρ (M ∙ B)      = rename ρ M ∙ B

_→ˢ_ : ∀ {Δ} → Ctx Δ → Ctx Δ → Set
_→ˢ_ Γ Γ' = ∀ {A} → Γ ∋ A → _ ; Γ' ⊢ A

ren : ∀ {Δ} {Γ Γ' : Ctx Δ} → Γ →ʳ Γ' → Γ →ˢ Γ'
ren ρ x = ` (ρ x)

infixr 6 _•_

_•_ : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  → Δ ; Γ' ⊢ A
  → Γ →ˢ Γ'
  → (Γ , A) →ˢ Γ'
(M • σ) Z      = M
(M • σ) (S x)  = σ x

id : ∀ {Δ} {Γ : Ctx Δ} → Γ →ˢ Γ
id x = ` x

↑ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} → Γ →ˢ (Γ , A)
↑ x = ` (S x)

⇑ : ∀ {Δ} {Γ : Ctx Δ} {A B : Type Δ}
  → Δ ; Γ ⊢ A
  → Δ ; Γ , B ⊢ A
⇑ M = rename S_ M

exts : ∀ {Δ} {Γ Δ' : Ctx Δ} {A : Type Δ}
  → Γ →ˢ Δ'
  → (Γ , A) →ˢ (Δ' , A)
exts σ Z      = ` Z
exts σ (S x)  = ⇑ (σ x)

exts-id-id : ∀ {Δ Γ A B} → exts {A = A} (id {Δ} {Γ}) {B} ≡ id {Δ} {Γ , A} {B}
exts-id-id = extensionality λ where
  Z      → refl
  (S x)  → refl
{-# REWRITE exts-id-id #-}

⇑ᵀ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} → Δ ; Γ ⊢ A → Δ ,α ; ⇑ᶜ Γ ⊢ renameᵗ S_ A
⇑ᵀ = renameᵀ S_

⇑ˢ : ∀ {Δ} {Γ Δ' : Ctx Δ}
  → Γ →ˢ Δ'
  → (⇑ᶜ Γ) →ˢ (⇑ᶜ Δ')
⇑ˢ {Γ = ∅} σ ()
⇑ˢ {Γ = Γ , A} σ Z       = ⇑ᵀ (σ Z)
⇑ˢ {Γ = Γ , A} σ (S x)   = ⇑ˢ (λ y → σ (S y)) x

private
  ⇑ʳ-S : ∀ {Δ} {Γ Γ' : Ctx Δ} {C : Type Δ} {B : Type (Δ ,α)}
    → (ρ : Γ →ʳ Γ')
    → (x : ⇑ᶜ Γ ∋ B)
    → ⇑ʳ (λ y → S_ {B = C} (ρ y)) x ≡ S_ {B = renameᵗ S_ C} (⇑ʳ ρ x)
  ⇑ʳ-S {Γ = ∅} ρ ()
  ⇑ʳ-S {Γ = Γ , A} ρ Z = refl
  ⇑ʳ-S {Γ = Γ , A} {Γ' = Γ'} {C = C} ρ (S x)
    rewrite ⇑ʳ-S {Γ = Γ} {Γ' = Γ'} {C = C} (λ y → ρ (S_ {B = A} y)) x = refl

⇑ʳ-id-id : ∀ {Δ Γ A} (x : ⇑ᶜ Γ ∋ A) → ⇑ʳ idʳ x ≡ idʳ {Δ = Δ ,α} {Γ = ⇑ᶜ Γ} x
⇑ʳ-id-id {Γ = ∅} ()
⇑ʳ-id-id {Γ = Γ , B} Z = refl
⇑ʳ-id-id {Δ} {Γ = Γ , B} (S x) rewrite ⇑ʳ-S {C = B} (idʳ {Δ} {Γ}) x
        | ⇑ʳ-id-id {Δ} {Γ} x = refl
{-# REWRITE ⇑ʳ-id-id #-}

private
  ⇑ˢ-ren : ∀ {Δ} {Γ Γ' : Ctx Δ} (ρ : Γ →ʳ Γ') {A}
    → (x : ⇑ᶜ Γ ∋ A)
    → ⇑ˢ (ren ρ) x ≡ ren (⇑ʳ ρ) x
  ⇑ˢ-ren {Γ = ∅} ρ ()
  ⇑ˢ-ren {Γ = Γ , B} ρ Z = refl
  ⇑ˢ-ren {Γ = Γ , B} ρ (S x) rewrite ⇑ˢ-ren (λ y → ρ (S y)) x = refl

⇑ˢ-id-id : ∀ {Δ Γ A} (x : ⇑ᶜ Γ ∋ A) → ⇑ˢ (id {Δ} {Γ}) x ≡ id {Δ = Δ ,α} {Γ = ⇑ᶜ Γ} x
⇑ˢ-id-id x rewrite ⇑ˢ-ren idʳ x | ⇑ʳ-id-id x = refl
{-# REWRITE ⇑ˢ-id-id #-}

subst : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  → Γ →ˢ Γ'
  → Δ ; Γ ⊢ A
  → Δ ; Γ' ⊢ A
subst σ `zero        = `zero
subst σ `true        = `true
subst σ `false       = `false
subst σ (`suc M)     = `suc (subst σ M)
subst σ (`case-nat L M N) = `case-nat (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (`if_then_else L M N) = `if_then_else (subst σ L) (subst σ M) (subst σ N)
subst σ (` x)        = σ x
subst σ (ƛ A ˙ N)    = ƛ A ˙ (subst (exts σ) N)
subst σ (L · M)      = subst σ L · subst σ M
subst σ (Λ N)        = Λ (subst (⇑ˢ σ) N)
subst σ (M ∙ B)      = subst σ M ∙ B

sub-id : ∀ {Δ Γ A} (M : Δ ; Γ ⊢ A)
    ---------------------------------
  → subst id M ≡ M
sub-id `zero = refl
sub-id `true = refl
sub-id `false = refl
sub-id (`suc M) rewrite sub-id M = refl
sub-id (`case-nat L M N) rewrite sub-id L | sub-id M = cong (`case-nat L M) (sub-id N)
sub-id (`if_then_else L M N) rewrite sub-id L | sub-id M | sub-id N = refl
sub-id (` x) = refl
sub-id (ƛ A ˙ M) = cong (ƛ A ˙_) (sub-id M)
sub-id (M · M₁) rewrite sub-id M | sub-id M₁ = refl
sub-id (Λ M) = cong Λ_ (sub-id M)
sub-id (M ∙ B) rewrite sub-id M = refl
{-# REWRITE sub-id #-}

extsᵗ-idᵗ-id : ∀ {Δ} → extsᵗ (idᵗ {Δ}) ≡ idᵗ {Δ ,α}
extsᵗ-idᵗ-id = extensionality λ where
  Z      → refl
  (S α)  → refl
{-# REWRITE extsᵗ-idᵗ-id #-}

substCtx-idᵗ-id : ∀ {Δ} (Γ : Ctx Δ) → substCtx idᵗ Γ ≡ Γ
substCtx-idᵗ-id ∅ = refl
substCtx-idᵗ-id (Γ , A) rewrite substCtx-idᵗ-id Γ = refl
{-# REWRITE substCtx-idᵗ-id #-}

sub-idᵀ : ∀ {Δ Γ A} (M : Δ ; Γ ⊢ A)
    ---------------------------------
  → substᵀ idᵗ M ≡ M
sub-idᵀ `zero = refl
sub-idᵀ `true = refl
sub-idᵀ `false = refl
sub-idᵀ (`suc M) rewrite sub-idᵀ M = refl
sub-idᵀ (`case-nat L M N) rewrite sub-idᵀ L | sub-idᵀ M | sub-idᵀ N = refl
sub-idᵀ (`if_then_else L M N) rewrite sub-idᵀ L | sub-idᵀ M | sub-idᵀ N = refl
sub-idᵀ (` x) = cong `_ (substᵗ-∋-idᵗ x)
  where
  substᵗ-∋-idᵗ : ∀ {Δ Γ A} (x : Γ ∋ A) → substᵗ-∋ (idᵗ {Δ}) x ≡ x
  substᵗ-∋-idᵗ Z      = refl
  substᵗ-∋-idᵗ (S x)  = cong S_ (substᵗ-∋-idᵗ x)
sub-idᵀ (ƛ A ˙ M) = cong (ƛ A ˙_) (sub-idᵀ M)
sub-idᵀ (M · M₁) rewrite sub-idᵀ M | sub-idᵀ M₁ = refl
sub-idᵀ (Λ M) = cong Λ_ (sub-idᵀ M)
sub-idᵀ (M ∙ B) rewrite sub-idᵀ M = refl
{-# REWRITE sub-idᵀ #-}

infixr 5 _⨟_

_⨟_ : ∀ {Δ} {Γ₁ Γ₂ Γ₃ : Ctx Δ} → Γ₁ →ˢ Γ₂ → Γ₂ →ˢ Γ₃ → Γ₁ →ˢ Γ₃
(σ ⨟ τ) x = subst τ (σ x)

σ₀ : ∀ {Δ Γ A} → Δ ; Γ ⊢ A → (Γ , A) →ˢ Γ
σ₀ M = M • id

_[_] : ∀ {Δ} {Γ : Ctx Δ} {A B : Type Δ}
  → Δ ; Γ , A ⊢ B
  → Δ ; Γ ⊢ A
    ------------------
  → Δ ; Γ ⊢ B
_[_] N M = subst (σ₀ M) N

```

values     V ::= ... | Λα. M

```

----------------------------------------
-- | Values and reduction semantics | --
----------------------------------------

data Value : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} → Δ ; Γ ⊢ A → Set where

  V-zero : ∀ {Δ} {Γ : Ctx Δ}
      ---------------------------
    → Value (`zero {Γ = Γ})

  V-suc : ∀ {Δ} {Γ : Ctx Δ} {V : Δ ; Γ ⊢ `Nat}
    → Value V
      ---------------------------
    → Value (`suc V)

  V-true : ∀ {Δ} {Γ : Ctx Δ}
      ---------------------------
    → Value (`true {Γ = Γ})

  V-false : ∀ {Δ} {Γ : Ctx Δ}
      ----------------------------
    → Value (`false {Γ = Γ})

  V-ƛ : ∀ {Δ Γ A B} {N : Δ ; Γ , A ⊢ B}
      ------------------------------------
    → Value (ƛ A ˙ N)

  -- | New rule for System F | --
  V-Λ : ∀ {Δ Γ A} {N : Δ ,α ; ⇑ᶜ Γ ⊢ A}
      ------------------------------------
    → Value (Λ N)


data _—→_ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} → Δ ; Γ ⊢ A → Δ ; Γ ⊢ A → Set where

  ξ-suc : ∀ {Δ Γ} {M M′ : Δ ; Γ ⊢ `Nat}
    →     M —→ M′
      ---------------------
    → `suc M —→ `suc M′

  ξ-case-nat : ∀ {Δ Γ A} {L L′ : Δ ; Γ ⊢ `Nat} {M : Δ ; Γ ⊢ A} {N : Δ ; Γ , `Nat ⊢ A}
    →     L —→ L′
      -----------------------------------------------
    → `case-nat L M N —→ `case-nat L′ M N

  ξ-if : ∀ {Δ Γ A} {L L′ : Δ ; Γ ⊢ `Bool} {M N : Δ ; Γ ⊢ A}
    →     L —→ L′
      -------------------------------------------------
    → `if_then_else L M N —→ `if_then_else L′ M N

  ξ-·₁ : ∀ {Δ Γ A B} {L L′ : Δ ; Γ ⊢ A ⇒ B} {M}
    →     L —→ L′
      ---------------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Δ Γ A B} {V : Δ ; Γ ⊢ A ⇒ B} {M M′}
    →     Value V
    →     M —→ M′
      ------------------------
    → V · M —→ V · M′

  -- | New congruence rule for System F
  ξ-∙ : ∀ {Δ Γ A B} {M M′ : Δ ; Γ ⊢ `∀ A}
    →     M —→ M′
      ---------------------------------------
    → M ∙ B —→ M′ ∙ B

  β-ƛ : ∀ {Δ Γ A B} {N : Δ ; Γ , A ⊢ B} {W}
    →          Value W
      ------------------------------
    → (ƛ A ˙ N) · W —→ N [ W ]

  β-zero :  ∀ {Δ Γ A} {M : Δ ; Γ ⊢ A} {N : Δ ; Γ , `Nat ⊢ A}
      ------------------------------------------
    → `case-nat `zero M N —→ M

  β-suc : ∀ {Δ Γ A} {V : Δ ; Γ ⊢ `Nat} {M : Δ ; Γ ⊢ A} {N : Δ ; Γ , `Nat ⊢ A}
    → Value V
      ------------------------------------------------
    → `case-nat (`suc V) M N —→ N [ V ]

  β-true : ∀ {Δ Γ A} {M N : Δ ; Γ ⊢ A}
      ------------------------------------------
    → `if_then_else `true M N —→ M

  β-false : ∀ {Δ Γ A} {M N : Δ ; Γ ⊢ A}
      -------------------------------------------
    → `if_then_else `false M N —→ N

  -- | New beta rule for System F
  β-Λ : ∀ {Δ Γ A B} {N : Δ ,α ; ⇑ᶜ Γ ⊢ A}
      ---------------------------------------
    → (Λ N) ∙ B —→ N [ B ]ᵀ

------------------
-- | Progress | --
------------------

data Progress {A} (M : ∅ ; ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ; ∅ ⊢ A}
    → M —→ N
      ------------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A} → (M : ∅ ; ∅ ⊢ A) → Progress M
progress `zero = done V-zero
progress `true = done V-true
progress `false = done V-false
progress (`suc M) = case progress M of λ where
  (step M→M′) → step (ξ-suc M→M′)
  (done vM) → done (V-suc vM)
progress (`case-nat L M N) = case progress L of λ where
  (step L→L′) → step (ξ-case-nat L→L′)
  (done V-zero) → step β-zero
  (done (V-suc vL)) → step (β-suc vL)
progress (`if_then_else L M N) = case progress L of λ where
  (step L→L′) → step (ξ-if L→L′)
  (done V-true) → step β-true
  (done V-false) → step β-false
progress (ƛ A ˙ N) = done V-ƛ
progress (Λ N) = done V-Λ
progress (L · M) = case progress L of λ where
  (step L→L′) → step (ξ-·₁ L→L′)
  (done vL) → case progress M of λ where
    (step M→M′) → step (ξ-·₂ vL M→M′)
    (done vM) → case vL of λ where
      V-ƛ → step (β-ƛ vM)
progress (M ∙ B) = case progress M of λ where
  (step M→M′) → step (ξ-∙ M→M′)
  (done vM) → case vM of λ where
    V-Λ → step β-Λ

infix 2 _—↠_

data _—↠_ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} → Δ ; Γ ⊢ A → Δ ; Γ ⊢ A → Set where
  _∎ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} (M : Δ ; Γ ⊢ A) → M —↠ M

  _—→⟨_⟩_ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
    (L : Δ ; Γ ⊢ A) {M N : Δ ; Γ ⊢ A}
    → L —→ M
    → M —↠ N
    → L —↠ N

↠-trans : ∀ {Δ Γ A} {L M N : Δ ; Γ ⊢ A}
  → L —↠ M
  → M —↠ N
  → L —↠ N
↠-trans (L ∎) M—↠N = M—↠N
↠-trans (L —→⟨ L—→M ⟩ Lrest) M—↠N = L —→⟨ L—→M ⟩ (↠-trans Lrest M—↠N)

step-eq-↠ : ∀ {Δ Γ A} {L M N : Δ ; Γ ⊢ A}
  → L —→ M
  → M ≡ N
  → L —↠ N
step-eq-↠ {M = M} L—→M refl = _ —→⟨ L—→M ⟩ (M ∎)

suc-↠ : ∀ {Δ Γ} {M M′ : Δ ; Γ ⊢ `Nat}
  → M —↠ M′
  → `suc M —↠ `suc M′
suc-↠ (M ∎) = (`suc M) ∎
suc-↠ (M —→⟨ M—→M′ ⟩ M′—↠M″) =
  (`suc M) —→⟨ ξ-suc M—→M′ ⟩ suc-↠ M′—↠M″

case-nat-↠ : ∀ {Δ Γ A} {L L′ : Δ ; Γ ⊢ `Nat} {M : Δ ; Γ ⊢ A} {N : Δ ; Γ , `Nat ⊢ A}
  → L —↠ L′
  → `case-nat L M N —↠ `case-nat L′ M N
case-nat-↠ {M = M} {N = N} (L ∎) = `case-nat L M N ∎
case-nat-↠ {M = M} {N = N} (L —→⟨ L—→L′ ⟩ L′—↠L″) =
  `case-nat L M N —→⟨ ξ-case-nat L—→L′ ⟩ case-nat-↠ {M = M} {N = N} L′—↠L″

if-↠ : ∀ {Δ Γ A} {L L′ : Δ ; Γ ⊢ `Bool} {M N : Δ ; Γ ⊢ A}
  → L —↠ L′
  → `if_then_else L M N —↠ `if_then_else L′ M N
if-↠ {M = M} {N = N} (L ∎) = `if_then_else L M N ∎
if-↠ {M = M} {N = N} (L —→⟨ L—→L′ ⟩ L′—↠L″) =
  `if_then_else L M N —→⟨ ξ-if L—→L′ ⟩ if-↠ {M = M} {N = N} L′—↠L″

·₁-↠ : ∀ {Δ Γ A B} {L L′ : Δ ; Γ ⊢ A ⇒ B} {M}
  → L —↠ L′
  → L · M —↠ L′ · M
·₁-↠ {M = M} (L ∎) = (L · M) ∎
·₁-↠ {M = M} (L —→⟨ L—→L′ ⟩ L′—↠L″) = (L · M) —→⟨ ξ-·₁ L—→L′ ⟩ ·₁-↠ {M = M} L′—↠L″

·₂-↠ : ∀ {Δ Γ A B} {V : Δ ; Γ ⊢ A ⇒ B} {M M′}
  → Value V
  → M —↠ M′
  → V · M —↠ V · M′
·₂-↠ {V = V} vV (M ∎) = (V · M) ∎
·₂-↠ {V = V} vV (M —→⟨ M—→M′ ⟩ M′—↠M″) = (V · M) —→⟨ ξ-·₂ vV M—→M′ ⟩ ·₂-↠ vV M′—↠M″

∙-↠ : ∀ {Δ Γ A B} {M M′ : Δ ; Γ ⊢ `∀ A}
  → M —↠ M′
  → M ∙ B —↠ M′ ∙ B
∙-↠ {B = B} (M ∎) = (M ∙ B) ∎
∙-↠ {B = B} (M —→⟨ M—→M′ ⟩ M′—↠M″) = (M ∙ B) —→⟨ ξ-∙ M—→M′ ⟩ ∙-↠ {B = B} M′—↠M″
```

Parametricity: the language does not allow programs that inspect values whose types are
type variables. Because of that, polymorphic functions of the same type take related
inputs to related outputs.

(The Agda code below is based on the lecture notes at
https://www.cs.uoregon.edu/research/summerschool/summer16/notes/AhmedLR.pdf)

We do not require much of the following relation. It has to be a set of pairs of values,
and the values in every pair of the relation have to be closed and well typed under
the corresponding type:

```
Rel : Type ∅ → Type ∅ → Set₁
Rel A B = (V : ∅ ; ∅ ⊢ A) → (W : ∅ ; ∅ ⊢ B) → Value V → Value W → Set
```

We define relational substitution ρ with projections to the
left type substitution, right type substitution, and the relation
assigned to each type variable.

```
record RelSub (Δ : TyCtx) : Set₁ where
  field
    ρ₁ : Δ ⇒ˢ ∅
    ρ₂ : Δ ⇒ˢ ∅
    ρR : ∀ α → Rel (ρ₁ α) (ρ₂ α)

open RelSub public

emptyRelSub : RelSub ∅
(emptyRelSub .ρ₁) = idᵗ
(emptyRelSub .ρ₂) = idᵗ
(emptyRelSub .ρR) ()

extendRelSub : ∀ {Δ}
  → (ρ : RelSub Δ)
  → (A₁ A₂ : Type ∅)
  → Rel A₁ A₂
  → RelSub (Δ ,α)
(extendRelSub ρ A₁ A₂ R) .ρ₁        = A₁ •ᵗ ρ₁ ρ
(extendRelSub ρ A₁ A₂ R) .ρ₂        = A₂ •ᵗ ρ₂ ρ
(extendRelSub ρ A₁ A₂ R) .ρR Z      = R
(extendRelSub ρ A₁ A₂ R) .ρR (S α)  = ρR ρ α
```

We then define the interpretation of values and expressions.
(Recall that logical relations are type-indexed inductive
relations.)

```
ValueRel : ∀ {Δ}
  → (A : Type Δ)
  → (ρ : RelSub Δ)
  → (V : ∅ ; ∅ ⊢ substᵗ (ρ₁ ρ) A)
  → (W : ∅ ; ∅ ⊢ substᵗ (ρ₂ ρ) A)
  → Value V
  → Value W
  → Set₁

ExprRel : ∀ {Δ}
  → (A : Type Δ)
  → (ρ : RelSub Δ)
  → ∅ ; ∅ ⊢ substᵗ (ρ₁ ρ) A
  → ∅ ; ∅ ⊢ substᵗ (ρ₂ ρ) A
  → Set₁

ValueRel (` α) ρ V W v w = Lift _ (ρR ρ α V W v w)
ValueRel `Nat ρ `zero `zero V-zero V-zero = Lift _ ⊤
ValueRel `Nat ρ `zero (`suc W) V-zero (V-suc w) = Lift _ ⊥
ValueRel `Nat ρ (`suc V) `zero (V-suc v) V-zero = Lift _ ⊥
ValueRel `Nat ρ (`suc V) (`suc W) (V-suc v) (V-suc w) = ValueRel `Nat ρ V W v w
ValueRel `Bool ρ `true `true V-true V-true = Lift _ ⊤
ValueRel `Bool ρ `true `false V-true V-false = Lift _ ⊥
ValueRel `Bool ρ `false `true V-false V-true = Lift _ ⊥
ValueRel `Bool ρ `false `false V-false V-false = Lift _ ⊤
ValueRel (A ⇒ B) ρ (ƛ _ ˙ N) (ƛ _ ˙ M) V-ƛ V-ƛ =
  ∀ {V W} (v : Value V) (w : Value W)
   → ValueRel A ρ V W v w
   → ExprRel B ρ (N [ V ]) (M [ W ])
ValueRel (`∀ A) ρ (Λ N) (Λ M) V-Λ V-Λ =
  ∀ (A₁ A₂ : Type ∅)
   → (R : Rel A₁ A₂)
   → ExprRel A (extendRelSub ρ A₁ A₂ R) (N [ A₁ ]ᵀ) (M [ A₂ ]ᵀ)

-- Both terms reduce to values related by the value interpretation
ExprRel A ρ M N =
  ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
    (M —↠ V) × (N —↠ W) × ValueRel A ρ V W v w
```

We also need the closing (term variable) substitutions:

```
record RelEnv {Δ} (Γ : Ctx Δ) (ρ : RelSub Δ) : Set₁ where
  field
    γ₁ : substCtx (ρ₁ ρ) Γ →ˢ ∅
    γ₂ : substCtx (ρ₂ ρ) Γ →ˢ ∅

open RelEnv public

emptyRelEnv : ∀ {ρ : RelSub ∅} → RelEnv ∅ ρ
(emptyRelEnv .γ₁) = id
(emptyRelEnv .γ₂) = id
```

Δ ; Γ ⊢ M ≈ N : A ≜
  (Δ ; Γ ⊢ M : A) ∧ (Δ ; Γ ⊢ N : A) ∧ (∀ ρ. ∀ γ. (ρ₁ (γ₁ M) , ρ₂ (γ₂ N)) ∈ ℰ⟦ A ⟧ ρ)

```
LogicalRel : ∀ {Δ Γ A} → (M N : Δ ; Γ ⊢ A) → Set₁
LogicalRel {Δ} {Γ} {A} M N = ∀ (ρ : RelSub Δ) (γ : RelEnv Γ ρ)
  → ExprRel A ρ (subst (γ .γ₁) (substᵀ (ρ .ρ₁) M)) (subst (γ .γ₂) (substᵀ (ρ .ρ₂) N))
```

With the logical relation defined, we state the fundamental property:

```
-- Fundamental Property: every well-typed term is related to itself.
postulate
  fundamental : ∀ {Δ Γ A} (M : Δ ; Γ ⊢ A) → LogicalRel M M
```

The fundamental property is quite strong. This is because closing the term off
with different ρ and γ may give us very different programs.

```

-- | Termination is a direct corollary of fundamental
terminate : ∀ {A}
  → (M : ∅ ; ∅ ⊢ A)
  → ∃[ V ] (M —↠ V) × Value V
terminate M = case fundamental M emptyRelSub emptyRelEnv of λ where
  ⟨ V , ⟨ _ , ⟨ v , ⟨ _ , ⟨ M↠V , _ ⟩ ⟩ ⟩ ⟩ ⟩ → ⟨ V , ⟨ M↠V , v ⟩ ⟩

-- | Free theorem (identity):

-- R = {(V, V)}
idR : ∀ {A} → (V : ∅ ; ∅ ⊢ A) → Rel A A
idR V V′ W′ _ _ = V ≡ V′ × V ≡ W′

free-theorem-id : ∀ {A : Type ∅}
  → (M : ∅ ; ∅ ⊢ `∀ (` Z ⇒ ` Z))
  → (V : ∅ ; ∅ ⊢ A)
  → Value V
    ------------------------
  → (M ∙ A) · V —↠ V
free-theorem-id {A} M V v =
  case fundamental M emptyRelSub emptyRelEnv of λ where
  ⟨ Λ N₁ , ⟨ Λ N₂ , ⟨ V-Λ , ⟨ V-Λ , ⟨ M↠ΛN₁ , ⟨ M↠ΛN₂ , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
    case rel A A (idR V) of λ where
    ⟨ ƛ _ ˙ N₁′ , ⟨ ƛ _ ˙ N₂′ , ⟨ V-ƛ , ⟨ V-ƛ , ⟨ N₁[A]↠ƛN₁′ , ⟨ N₂[A]↠ƛN₂′ , rel′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
      case rel′ v v (lift ⟨ refl , refl ⟩) of λ where
      ⟨ W₁ , ⟨ W₂ , ⟨ w₁ , ⟨ w₂ , ⟨ N₁′[V]↠W₁ , ⟨ N₂′[V]↠W₂ , lift ⟨ refl , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
         ↠-trans (·₁-↠ (∙-↠ M↠ΛN₁))
        (↠-trans (((Λ N₁ ∙ A) · V) —→⟨ ξ-·₁ β-Λ ⟩ (((N₁ [ A ]ᵀ) · V) ∎))
        (↠-trans (·₁-↠ N₁[A]↠ƛN₁′)
        (↠-trans (((ƛ _ ˙ N₁′) · V) —→⟨ β-ƛ v ⟩ ((N₁′ [ V ]) ∎)) N₁′[V]↠W₁)))

-- | Free theorem (representation independence):

neg : ∅ ; ∅ ⊢ (`Bool ⇒ `Bool)
neg = ƛ `Bool ˙ `if ` Z then `false else `true

flip : ∅ ; ∅ ⊢ (`Nat ⇒ `Nat)
flip = ƛ `Nat ˙ `case-nat (` Z) (`suc `zero) `zero

-- R = {(true, 1), (false, 0)}
R : Rel `Bool `Nat
R `true `zero V-true V-zero = ⊥
R `true (`suc `zero) V-true (V-suc V-zero) = ⊤
R `true (`suc (`suc W)) V-true (V-suc (V-suc w)) = ⊥
R `false `zero V-false V-zero = ⊤
R `false (`suc W) V-false (V-suc w) = ⊥

neg-flip-related : ValueRel (` Z ⇒ ` Z) (extendRelSub emptyRelSub `Bool `Nat R) neg flip V-ƛ V-ƛ
neg-flip-related {V = `true} {W = `zero} V-true V-zero (lift ())
neg-flip-related {V = `true} {W = `suc `zero} V-true (V-suc V-zero) (lift tt) =
  ⟨ `false , ⟨ `zero , ⟨ V-false , ⟨ V-zero ,
    ⟨ (`if `true then `false else `true) —→⟨ β-true ⟩ (`false ∎) ,
      ⟨ (`case-nat (`suc `zero) (`suc `zero) `zero) —→⟨ β-suc V-zero ⟩ (`zero ∎) ,
        lift tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related {V = `true} {W = `suc (`suc W)} V-true (V-suc (V-suc w)) (lift ())
neg-flip-related {V = `false} {W = `zero} V-false V-zero (lift tt) =
  ⟨ `true , ⟨ `suc `zero , ⟨ V-true , ⟨ V-suc V-zero ,
    ⟨ (`if `false then `false else `true) —→⟨ β-false ⟩ (`true ∎) ,
      ⟨ (`case-nat `zero (`suc `zero) `zero) —→⟨ β-zero ⟩ ((`suc `zero) ∎) ,
        lift tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related {V = `false} {W = `suc W} V-false (V-suc w) (lift ())

-- If ∅ ; ∅ ⊢ M : ∀ α. α -> (α -> α) -> α,
-- then M [ Bool ] true neg —↠ V
-- and  M [ Nat  ] 1   flip —↠ W
-- and  (V, W) ∈ R.
free-theorem-rep :
  ∀ (M : ∅ ; ∅ ⊢ `∀ (` Z ⇒ (` Z ⇒ ` Z) ⇒ ` Z))
    ------------------------------------------------------
  → ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
        ((M ∙ `Bool · `true)        · neg  —↠ V)
      × ((M ∙ `Nat  · (`suc `zero)) · flip —↠ W)
      × Lift _ (R V W v w)
free-theorem-rep M =
  case fundamental M emptyRelSub emptyRelEnv of λ where
  ⟨ Λ N₁ , ⟨ Λ N₂ , ⟨ V-Λ , ⟨ V-Λ , ⟨ M↠ΛN₁ , ⟨ M↠ΛN₂ , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
    case rel `Bool `Nat R of λ where
    ⟨ ƛ _ ˙ N₁′ , ⟨ ƛ _ ˙ N₂′ , ⟨ V-ƛ , ⟨ V-ƛ , ⟨ N₁[Bool]↠ƛN₁′ , ⟨ N₂[Nat]↠ƛN₂′ , rel₁ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
      case rel₁ V-true (V-suc V-zero) (lift tt) of λ where
      ⟨ ƛ _ ˙ N₁″ , ⟨ ƛ _ ˙ N₂″ , ⟨ V-ƛ , ⟨ V-ƛ , ⟨ N₁′[true]↠ƛN₁″ , ⟨ N₂′[one]↠ƛN₂″ , rel₂ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
        case rel₂ {V = neg} {W = flip} V-ƛ V-ƛ neg-flip-related of λ where
        ⟨ V , ⟨ W , ⟨ v , ⟨ w ,
          ⟨ N₁″[neg]↠V , ⟨ N₂″[flip]↠W , VW∈R ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
          ⟨ V , ⟨ W , ⟨ v , ⟨ w ,
            ⟨ (↠-trans
                 (↠-trans
                   (·₁-↠ (·₁-↠ (∙-↠ M↠ΛN₁)))
                   (↠-trans
                     (step-eq-↠ (ξ-·₁ (ξ-·₁ β-Λ)) refl)
                     (↠-trans
                       (·₁-↠ (·₁-↠ N₁[Bool]↠ƛN₁′))
                       (↠-trans
                         (step-eq-↠ (ξ-·₁ (β-ƛ V-true)) refl)
                         (↠-trans
                           (·₁-↠ N₁′[true]↠ƛN₁″)
                           (step-eq-↠ (β-ƛ V-ƛ) refl))))))
                 N₁″[neg]↠V)
            , ⟨ (↠-trans
                   (↠-trans
                     (·₁-↠ (·₁-↠ (∙-↠ M↠ΛN₂)))
                     (↠-trans
                       (step-eq-↠ (ξ-·₁ (ξ-·₁ β-Λ)) refl)
                       (↠-trans
                         (·₁-↠ (·₁-↠ N₂[Nat]↠ƛN₂′))
                         (↠-trans
                           (step-eq-↠ (ξ-·₁ (β-ƛ (V-suc V-zero))) refl)
                           (↠-trans
                             (·₁-↠ N₂′[one]↠ƛN₂″)
                             (step-eq-↠ (β-ƛ V-ƛ) refl))))))
                   N₂″[flip]↠W)
              , VW∈R ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
```

(Exercise) Add pairs to the calculus and prove that "swap" swaps
as a free theorem:
If ∅ ; ∅ ⊢ M : ∀ α. ∀ β. α × β → β × α and ∅ ; ∅ ⊢ V : A and ∅ ; ∅ ⊢ W : B
then M [ A ] [ B ] ⟨ V , W ⟩ —↠ ⟨ W , V ⟩
