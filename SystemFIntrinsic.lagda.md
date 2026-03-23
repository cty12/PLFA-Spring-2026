```
{-# OPTIONS --rewriting #-}

module SystemFIntrinsic where

-- Need the following two imports for rewriting
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
open import Function using (case_of_)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

System F: STLC with universal types

types      A ::= ... | α | ∀α. A
terms      M ::= ... | Λα. M | M [ A ]  (in the Agda code below, we use _∙_ for type application)

```

infixr 8 _`×_
infixr 7 _⇒_
infixr 6 _•ᵗ_
infixl 5 _,_
infix  4 _∋_
infix  4 _;_⊢_

infix  9 `_
infix  5 ƛ_˙_
infixl 7 _·_
infixl 7 _∙_

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
  _⇒_    : ∀ {Δ} → Type Δ → Type Δ → Type Δ
  _`×_   : ∀ {Δ} → Type Δ → Type Δ → Type Δ
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
renameᵗ ρ (A ⇒ B)  = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (A `× B)  = renameᵗ ρ A `× renameᵗ ρ B
renameᵗ ρ (`∀ A)  = `∀ (renameᵗ (extᵗ ρ) A)

renameᵗ-cong : ∀ {Δ Δ'} {ρ ρ' : Δ ⇒ʳ Δ'} (A : Type Δ)
  → (∀ α → ρ α ≡ ρ' α)
    ---------------------------------
  → renameᵗ ρ A ≡ renameᵗ ρ' A
renameᵗ-cong (` α) eq = cong `_ (eq α)
renameᵗ-cong `Nat _ = refl
renameᵗ-cong (A ⇒ B) eq rewrite renameᵗ-cong A eq | renameᵗ-cong B eq = refl
renameᵗ-cong (A `× B) eq rewrite renameᵗ-cong A eq | renameᵗ-cong B eq = refl
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
renameᵗ-comp ρ₁ ρ₂ (A ⇒ B)
  rewrite renameᵗ-comp ρ₁ ρ₂ A | renameᵗ-comp ρ₁ ρ₂ B = refl
renameᵗ-comp ρ₁ ρ₂ (A `× B)
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

infixr 5 _⨟ᵗ_

substᵗ : ∀ {Δ Δ'} → Δ ⇒ˢ Δ' → Type Δ → Type Δ'
substᵗ σ (` x)   = σ x
substᵗ σ `Nat     = `Nat
substᵗ σ (A ⇒ B)  = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (A `× B)  = substᵗ σ A `× substᵗ σ B
substᵗ σ (`∀ A)  = `∀ (substᵗ (extsᵗ σ) A)

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
substᵗ-cong (A ⇒ B) eq rewrite substᵗ-cong A eq | substᵗ-cong B eq = refl
substᵗ-cong (A `× B) eq rewrite substᵗ-cong A eq | substᵗ-cong B eq = refl
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
ren-subᵗ ρ σ (A ⇒ B) rewrite ren-subᵗ ρ σ A | ren-subᵗ ρ σ B = refl
ren-subᵗ ρ σ (A `× B) rewrite ren-subᵗ ρ σ A | ren-subᵗ ρ σ B = refl
ren-subᵗ ρ σ (`∀ A)   rewrite ren-subᵗ (extᵗ ρ) (extsᵗ σ) A = refl
{-# REWRITE ren-subᵗ #-}

sub-idᵗ : ∀ {Δ} (A : Type Δ) → substᵗ idᵗ A ≡ A
sub-idᵗ (` x)    = refl
sub-idᵗ `Nat     = refl
sub-idᵗ (A ⇒ B)  rewrite sub-idᵗ A | sub-idᵗ B = refl
sub-idᵗ (A `× B)  rewrite sub-idᵗ A | sub-idᵗ B = refl
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
sub-renᵗ ρ σ (A ⇒ B) rewrite sub-renᵗ ρ σ A | sub-renᵗ ρ σ B = refl
sub-renᵗ ρ σ (A `× B) rewrite sub-renᵗ ρ σ A | sub-renᵗ ρ σ B = refl
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
sub-subᵗ σ τ (A ⇒ B) rewrite sub-subᵗ σ τ A | sub-subᵗ σ τ B = refl
sub-subᵗ σ τ (A `× B) rewrite sub-subᵗ σ τ A | sub-subᵗ σ τ B = refl
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

  `zero :
      --------------- (T-Zero)
    Δ ; Γ ⊢ `Nat

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

  `⟨_,_⟩ : ∀ {A B}
    → Δ ; Γ ⊢ A
    → Δ ; Γ ⊢ B
      ------------------ (T-Pair)
    → Δ ; Γ ⊢ A `× B

  `proj₁ : ∀ {A B}
    → Δ ; Γ ⊢ A `× B
      ------------------ (T-ProjFirst)
    → Δ ; Γ ⊢ A

  `proj₂ : ∀ {A B}
    → Δ ; Γ ⊢ A `× B
      ------------------ (T-ProjSecond)
    → Δ ; Γ ⊢ B

  -- | New rules for System F | --
  Λ_ : ∀ {A}
    → Δ ,α ; ⇑ᶜ Γ ⊢ A
      --------------------- (T-TAbs)
    → Δ ; Γ ⊢ `∀ A

  _∙_    : ∀ {A}
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
renameᵀ ρ (` x)         = ` (renameᵗ-∋ ρ x)
renameᵀ ρ (ƛ A ˙ N)     = ƛ renameᵗ ρ A ˙ (renameᵀ ρ N)
renameᵀ ρ (L · M)       = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ (`⟨ L , M ⟩)  = `⟨ renameᵀ ρ L , renameᵀ ρ M ⟩
renameᵀ ρ (`proj₁ M)    = `proj₁ (renameᵀ ρ M)
renameᵀ ρ (`proj₂ M)    = `proj₂ (renameᵀ ρ M)
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
substᵀ σ (` x)             = ` (substᵗ-∋ σ x)
substᵀ σ (ƛ A ˙ N)         = ƛ substᵗ σ A ˙ (substᵀ σ N)
substᵀ σ (L · M)           = substᵀ σ L · substᵀ σ M
substᵀ σ (`⟨ L , M ⟩)      = `⟨ substᵀ σ L , substᵀ σ M ⟩
substᵀ σ (`proj₁ M)        = `proj₁ (substᵀ σ M)
substᵀ σ (`proj₂ M)        = `proj₂ (substᵀ σ M)
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
rename ρ (` x)        = ` (ρ x)
rename ρ (ƛ _ ˙ N)    = ƛ _ ˙ (rename (ext ρ) N)
rename ρ (L · M)      = rename ρ L · rename ρ M
rename ρ (`⟨ L , M ⟩) = `⟨ rename ρ L , rename ρ M ⟩
rename ρ (`proj₁ M)   = `proj₁ (rename ρ M)
rename ρ (`proj₂ M)   = `proj₂ (rename ρ M)
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
subst σ (` x)        = σ x
subst σ (ƛ A ˙ N)    = ƛ A ˙ (subst (exts σ) N)
subst σ (L · M)      = subst σ L · subst σ M
subst σ (`⟨ L , M ⟩) = `⟨ subst σ L , subst σ M ⟩
subst σ (`proj₁ M)   = `proj₁ (subst σ M)
subst σ (`proj₂ M)   = `proj₂ (subst σ M)
subst σ (Λ N)        = Λ (subst (⇑ˢ σ) N)
subst σ (M ∙ B)      = subst σ M ∙ B

subst-cong : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ} {σ τ : Γ →ˢ Γ'}
  → (∀ {B} (x : Γ ∋ B) → σ x ≡ τ x)
  → (M : Δ ; Γ ⊢ A)
  → subst σ M ≡ subst τ M
subst-cong σ≡τ `zero         = refl
subst-cong σ≡τ (` x)         = σ≡τ x
subst-cong σ≡τ (ƛ A ˙ M)     = cong (ƛ A ˙_) (subst-cong σ≡τ′ M)
  where
  σ≡τ′ : ∀ {B} (x : _ , A ∋ B) → exts _ x ≡ exts _ x
  σ≡τ′ Z      = refl
  σ≡τ′ (S x)  = cong ⇑ (σ≡τ x)
subst-cong σ≡τ (L · M)       = cong₂ _·_ (subst-cong σ≡τ L) (subst-cong σ≡τ M)
subst-cong σ≡τ (`⟨ L , M ⟩)  = cong₂ `⟨_,_⟩ (subst-cong σ≡τ L) (subst-cong σ≡τ M)
subst-cong σ≡τ (`proj₁ M)    = cong `proj₁ (subst-cong σ≡τ M)
subst-cong σ≡τ (`proj₂ M)    = cong `proj₂ (subst-cong σ≡τ M)
subst-cong σ≡τ (Λ M)         = cong Λ_ (subst-cong (⇑ˢ-cong σ≡τ) M)
  where
  ⇑ˢ-cong : ∀ {Δ} {Γ Γ' : Ctx Δ} {σ τ : Γ →ˢ Γ'}
    → (∀ {A} (x : Γ ∋ A) → σ x ≡ τ x)
    → ∀ {A} (x : ⇑ᶜ Γ ∋ A) → ⇑ˢ σ x ≡ ⇑ˢ τ x
  ⇑ˢ-cong {Γ = ∅} σ≡τ ()
  ⇑ˢ-cong {Γ = Γ , B} σ≡τ Z      = cong ⇑ᵀ (σ≡τ Z)
  ⇑ˢ-cong {Γ = Γ , B} σ≡τ (S x)  = ⇑ˢ-cong (λ y → σ≡τ (S y)) x
subst-cong σ≡τ (M ∙ B)       = cong (λ N → N ∙ B) (subst-cong σ≡τ M)

sub-id : ∀ {Δ Γ A} (M : Δ ; Γ ⊢ A)
    ---------------------------------
  → subst id M ≡ M
sub-id `zero = refl
sub-id (` x) = refl
sub-id (ƛ A ˙ M) = cong (ƛ A ˙_) (sub-id M)
sub-id (M · M₁) rewrite sub-id M | sub-id M₁ = refl
sub-id `⟨ M , M₁ ⟩ rewrite sub-id M | sub-id M₁ = refl
sub-id (`proj₁ M) rewrite sub-id M = refl
sub-id (`proj₂ M) rewrite sub-id M = refl
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
sub-idᵀ (` x) = cong `_ (substᵗ-∋-idᵗ x)
  where
  substᵗ-∋-idᵗ : ∀ {Δ Γ A} (x : Γ ∋ A) → substᵗ-∋ (idᵗ {Δ}) x ≡ x
  substᵗ-∋-idᵗ Z      = refl
  substᵗ-∋-idᵗ (S x)  = cong S_ (substᵗ-∋-idᵗ x)
sub-idᵀ (ƛ A ˙ M) = cong (ƛ A ˙_) (sub-idᵀ M)
sub-idᵀ (M · M₁) rewrite sub-idᵀ M | sub-idᵀ M₁ = refl
sub-idᵀ `⟨ M , M₁ ⟩ rewrite sub-idᵀ M | sub-idᵀ M₁ = refl
sub-idᵀ (`proj₁ M) rewrite sub-idᵀ M = refl
sub-idᵀ (`proj₂ M) rewrite sub-idᵀ M = refl
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

  V-ƛ : ∀ {Δ Γ A B} {N : Δ ; Γ , A ⊢ B}
      ------------------------------------
    → Value (ƛ A ˙ N)

  V-⟨⟩ : ∀ {Δ Γ A B} {V : Δ ; Γ ⊢ A} {W : Δ ; Γ ⊢ B}
    → Value V
    → Value W
      ------------------------------------
    → Value (`⟨ V , W ⟩)

  -- | New rule for System F | --
  V-Λ : ∀ {Δ Γ A} {N : Δ ,α ; ⇑ᶜ Γ ⊢ A}
      ------------------------------------
    → Value (Λ N)


data _—→_ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} → Δ ; Γ ⊢ A → Δ ; Γ ⊢ A → Set where

  ξ-·₁ : ∀ {Δ Γ A B} {L L′ : Δ ; Γ ⊢ A ⇒ B} {M}
    →     L —→ L′
      ---------------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Δ Γ A B} {V : Δ ; Γ ⊢ A ⇒ B} {M M′}
    →     Value V
    →     M —→ M′
      ------------------------
    → V · M —→ V · M′

  ξ-⟨⟩₁ : ∀ {Δ Γ A B} {L L′ : Δ ; Γ ⊢ A} {M : Δ ; Γ ⊢ B}
    →     L —→ L′
      ---------------------------
    → `⟨ L , M ⟩ —→ `⟨ L′ , M ⟩

  ξ-⟨⟩₂ : ∀ {Δ Γ A B} {V : Δ ; Γ ⊢ A} {M M′ : Δ ; Γ ⊢ B}
    →     Value V
    →     M —→ M′
      ---------------------------
    → `⟨ V , M ⟩ —→ `⟨ V , M′ ⟩

  ξ-proj₁ : ∀ {Δ Γ A B} {M M′ : Δ ; Γ ⊢ A `× B}
    →     M —→ M′
      ---------------------
    → `proj₁ M —→ `proj₁ M′

  ξ-proj₂ : ∀ {Δ Γ A B} {M M′ : Δ ; Γ ⊢ A `× B}
    →     M —→ M′
      ---------------------
    → `proj₂ M —→ `proj₂ M′

  -- | New congruence rule for System F
  ξ-∙ : ∀ {Δ Γ A B} {M M′ : Δ ; Γ ⊢ `∀ A}
    →     M —→ M′
      ---------------------------------------
    → M ∙ B —→ M′ ∙ B

  β-ƛ : ∀ {Δ Γ A B} {N : Δ ; Γ , A ⊢ B} {W}
    →          Value W
      ------------------------------
    → (ƛ A ˙ N) · W —→ N [ W ]

  β-proj₁ : ∀ {Δ Γ A B} {V : Δ ; Γ ⊢ A} {W : Δ ; Γ ⊢ B}
    → Value V
    → Value W
      ---------------------------
    → `proj₁ `⟨ V , W ⟩ —→ V

  β-proj₂ : ∀ {Δ Γ A B} {V : Δ ; Γ ⊢ A} {W : Δ ; Γ ⊢ B}
    → Value V
    → Value W
      ---------------------------
    → `proj₂ `⟨ V , W ⟩ —→ W

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
progress (ƛ A ˙ N) = done V-ƛ
progress (`⟨ L , M ⟩) = case progress L of λ where
  (step L→L′) → step (ξ-⟨⟩₁ L→L′)
  (done vL) → case progress M of λ where
    (step M→M′) → step (ξ-⟨⟩₂ vL M→M′)
    (done vM) → done (V-⟨⟩ vL vM)
progress (`proj₁ M) = case progress M of λ where
  (step M→M′) → step (ξ-proj₁ M→M′)
  (done vM) → case vM of λ where
    (V-⟨⟩ vL vR) → step (β-proj₁ vL vR)
progress (`proj₂ M) = case progress M of λ where
  (step M→M′) → step (ξ-proj₂ M→M′)
  (done vM) → case vM of λ where
    (V-⟨⟩ vL vR) → step (β-proj₂ vL vR)
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

—↠-trans : ∀ {Δ Γ A} {L M N : Δ ; Γ ⊢ A}
  → L —↠ M
  → M —↠ N
  → L —↠ N
—↠-trans (L ∎) M—↠N = M—↠N
—↠-trans (L —→⟨ L—→M ⟩ Lrest) M—↠N = L —→⟨ L—→M ⟩ (—↠-trans Lrest M—↠N)

step-eq-↠ : ∀ {Δ Γ A} {L M N : Δ ; Γ ⊢ A}
  → L —→ M
  → M ≡ N
  → L —↠ N
step-eq-↠ {M = M} L—→M refl = _ —→⟨ L—→M ⟩ (M ∎)

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

⟨⟩₁-↠ : ∀ {Δ Γ A B} {L L′ : Δ ; Γ ⊢ A} {M : Δ ; Γ ⊢ B}
  → L —↠ L′
  → `⟨ L , M ⟩ —↠ `⟨ L′ , M ⟩
⟨⟩₁-↠ {M = M} (L ∎) = `⟨ L , M ⟩ ∎
⟨⟩₁-↠ {M = M} (L —→⟨ L—→L′ ⟩ L′—↠L″) =
  `⟨ L , M ⟩ —→⟨ ξ-⟨⟩₁ L—→L′ ⟩ ⟨⟩₁-↠ {M = M} L′—↠L″

⟨⟩₂-↠ : ∀ {Δ Γ A B} {V : Δ ; Γ ⊢ A} {M M′ : Δ ; Γ ⊢ B}
  → Value V
  → M —↠ M′
  → `⟨ V , M ⟩ —↠ `⟨ V , M′ ⟩
⟨⟩₂-↠ {V = V} vV (M ∎) = `⟨ V , M ⟩ ∎
⟨⟩₂-↠ {V = V} vV (M —→⟨ M—→M′ ⟩ M′—↠M″) =
  `⟨ V , M ⟩ —→⟨ ξ-⟨⟩₂ vV M—→M′ ⟩ ⟨⟩₂-↠ vV M′—↠M″

proj₁-↠ : ∀ {Δ Γ A B} {M M′ : Δ ; Γ ⊢ A `× B}
  → M —↠ M′
  → `proj₁ M —↠ `proj₁ M′
proj₁-↠ (M ∎) = `proj₁ M ∎
proj₁-↠ (M —→⟨ M—→M′ ⟩ M′—↠M″) =
  `proj₁ M —→⟨ ξ-proj₁ M—→M′ ⟩ proj₁-↠ M′—↠M″

proj₂-↠ : ∀ {Δ Γ A B} {M M′ : Δ ; Γ ⊢ A `× B}
  → M —↠ M′
  → `proj₂ M —↠ `proj₂ M′
proj₂-↠ (M ∎) = `proj₂ M ∎
proj₂-↠ (M —→⟨ M—→M′ ⟩ M′—↠M″) =
  `proj₂ M —→⟨ ξ-proj₂ M—→M′ ⟩ proj₂-↠ M′—↠M″

∙-↠ : ∀ {Δ Γ A B} {M M′ : Δ ; Γ ⊢ `∀ A}
  → M —↠ M′
  → M ∙ B —↠ M′ ∙ B
∙-↠ {B = B} (M ∎) = (M ∙ B) ∎
∙-↠ {B = B} (M —→⟨ M—→M′ ⟩ M′—↠M″) = (M ∙ B) —→⟨ ξ-∙ M—→M′ ⟩ ∙-↠ {B = B} M′—↠M″
```
