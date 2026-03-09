module SystemFIntrinsic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)

infixr 7 _⇒_
infixl 5 _,_
infix  4 _∋_
infix  4 _;_⊢_
infix  9 `_
infix  5 ƛ_˙_
infixl 7 _·_
infixl 7 _∙_
infix  2 _—→_

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

---------------
-- | Types | --
---------------

data Type : TyCtx → Set where
  `_    : ∀ {Δ} → TyVar Δ → Type Δ
  `Nat  : ∀ {Δ} → Type Δ
  _⇒_   : ∀ {Δ} → Type Δ → Type Δ → Type Δ
  ∀̇_    : ∀ {Δ} → Type (Δ ,α) → Type Δ

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
renameᵗ ρ (∀̇ A)  = ∀̇ (renameᵗ (extᵗ ρ) A)

renameᵗ-cong : ∀ {Δ Δ'} {ρ ρ' : Δ ⇒ʳ Δ'} (A : Type Δ)
  → (∀ α → ρ α ≡ ρ' α)
    ---------------------------------
  → renameᵗ ρ A ≡ renameᵗ ρ' A
renameᵗ-cong (` α) eq = cong `_ (eq α)
renameᵗ-cong `Nat _ = refl
renameᵗ-cong (A ⇒ B) eq rewrite renameᵗ-cong A eq | renameᵗ-cong B eq = refl
renameᵗ-cong {ρ = ρ} {ρ'} (∀̇ A) eq = cong ∀̇_ (renameᵗ-cong A ext-eq)
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
renameᵗ-comp ρ₁ ρ₂ (∀̇ A) = cong ∀̇_
    (trans (renameᵗ-comp (extᵗ ρ₁) (extᵗ ρ₂) A)
           (renameᵗ-cong A ext-comp))
  where
  ext-comp : ∀ α → extᵗ ρ₂ (extᵗ ρ₁ α) ≡ extᵗ (λ β → ρ₂ (ρ₁ β)) α
  ext-comp Z      = refl
  ext-comp (S α)  = refl

⇑ᵗ : ∀ {Δ} (A : Type Δ) → Type (Δ ,α)
⇑ᵗ = renameᵗ S_

renameᵗ-shift : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') (A : Type Δ)
  → renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
renameᵗ-shift ρ A rewrite renameᵗ-comp S_ (extᵗ ρ) A | renameᵗ-comp ρ S_ A = refl

infixr 7 _⇒ˢ_

_⇒ˢ_ : TyCtx → TyCtx → Set
Δ ⇒ˢ Δ' = TyVar Δ → Type Δ'

extsᵗ : ∀ {Δ Δ'} → Δ ⇒ˢ Δ' → (Δ ,α) ⇒ˢ (Δ' ,α)
extsᵗ σ Z      = ` Z
extsᵗ σ (S x)  = ⇑ᵗ (σ x)

σ₀ᵗ : ∀ {Δ} → Type Δ → (Δ ,α) ⇒ˢ Δ
σ₀ᵗ B Z      = B
σ₀ᵗ B (S x)  = ` x

substᵗ : ∀ {Δ Δ'} → Δ ⇒ˢ Δ' → Type Δ → Type Δ'
substᵗ σ (` x)   = σ x
substᵗ σ `Nat     = `Nat
substᵗ σ (A ⇒ B)  = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (∀̇ A)  = ∀̇ (substᵗ (extsᵗ σ) A)

substᵗ-cong : ∀ {Δ Δ'} {σ τ : Δ ⇒ˢ Δ'} A
  → (∀ α → σ α ≡ τ α)
    ------------------------------
  → substᵗ σ A ≡ substᵗ τ A
substᵗ-cong (` α) eq = eq α
substᵗ-cong `Nat _ = refl
substᵗ-cong (A ⇒ B) eq rewrite substᵗ-cong A eq | substᵗ-cong B eq = refl
substᵗ-cong {σ = σ} {τ} (∀̇ A) eq = cong ∀̇_ (substᵗ-cong A exts-eq)
  where
  exts-eq : ∀ α → extsᵗ σ α ≡ extsᵗ τ α
  exts-eq Z      = refl
  exts-eq (S α)  = cong ⇑ᵗ (eq α)

_[_]ᵗ : ∀ {Δ} → Type (Δ ,α) → Type Δ → Type Δ
A [ B ]ᵗ = substᵗ (σ₀ᵗ B) A

extsᵗ-extᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₁ ⇒ʳ Δ₂) (σ : Δ₂ ⇒ˢ Δ₃) α
    ------------------------------------------------------------
  → extsᵗ σ (extᵗ ρ α) ≡ extsᵗ (λ β → σ (ρ β)) α
extsᵗ-extᵗ ρ σ Z      = refl
extsᵗ-extᵗ ρ σ (S _)  = refl

substᵗ-renameᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₁ ⇒ʳ Δ₂) (σ : Δ₂ ⇒ˢ Δ₃) A
    ---------------------------------------------------------------
  → substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ α → σ (ρ α)) A
substᵗ-renameᵗ ρ σ (` α)  = refl
substᵗ-renameᵗ ρ σ `Nat   = refl
substᵗ-renameᵗ ρ σ (A ⇒ B) rewrite substᵗ-renameᵗ ρ σ A | substᵗ-renameᵗ ρ σ B = refl
substᵗ-renameᵗ ρ σ (∀̇ A) rewrite substᵗ-renameᵗ (extᵗ ρ) (extsᵗ σ) A
  | substᵗ-cong A (extsᵗ-extᵗ ρ σ) = refl

extᵗ-extsᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₂ ⇒ʳ Δ₃) (σ : Δ₁ ⇒ˢ Δ₂) α
    ------------------------------------------------------------------
  → renameᵗ (extᵗ ρ) (extsᵗ σ α) ≡ extsᵗ (λ β → renameᵗ ρ (σ β)) α
extᵗ-extsᵗ ρ σ Z      = refl
extᵗ-extsᵗ ρ σ (S α) rewrite renameᵗ-shift ρ (σ α) = refl

renameᵗ-substᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₂ ⇒ʳ Δ₃) (σ : Δ₁ ⇒ˢ Δ₂) A
    ---------------------------------------------------------------
  → renameᵗ ρ (substᵗ σ A) ≡ substᵗ (λ α → renameᵗ ρ (σ α)) A
renameᵗ-substᵗ ρ σ (` α)  = refl
renameᵗ-substᵗ ρ σ `Nat   = refl
renameᵗ-substᵗ ρ σ (A ⇒ B) rewrite renameᵗ-substᵗ ρ σ A | renameᵗ-substᵗ ρ σ B = refl
renameᵗ-substᵗ ρ σ (∀̇ A) rewrite renameᵗ-substᵗ (extᵗ ρ) (extsᵗ σ) A
  | substᵗ-cong A (extᵗ-extsᵗ ρ σ) = refl

substᵗ-shift : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') A
    ---------------------------------------------------
  → substᵗ (extsᵗ σ) (⇑ᵗ A) ≡ ⇑ᵗ (substᵗ σ A)
substᵗ-shift σ A rewrite substᵗ-renameᵗ S_ (extsᵗ σ) A
  | sym (renameᵗ-substᵗ S_ σ A) = refl

extsᵗ-substᵗ : ∀ {Δ₁ Δ₂ Δ₃} (σ : Δ₁ ⇒ˢ Δ₂) (τ : Δ₂ ⇒ˢ Δ₃) α
    ------------------------------------------------------------------
  → substᵗ (extsᵗ τ) (extsᵗ σ α) ≡ extsᵗ (λ β → substᵗ τ (σ β)) α
extsᵗ-substᵗ σ τ Z      = refl
extsᵗ-substᵗ σ τ (S x) rewrite substᵗ-shift τ (σ x) = refl

substᵗ-comp : ∀ {Δ₁ Δ₂ Δ₃} (σ : Δ₁ ⇒ˢ Δ₂) (τ : Δ₂ ⇒ˢ Δ₃) A
    ---------------------------------------------------------------
  → substᵗ τ (substᵗ σ A) ≡ substᵗ (λ x → substᵗ τ (σ x)) A
substᵗ-comp σ τ (` α)   = refl
substᵗ-comp σ τ `Nat    = refl
substᵗ-comp σ τ (A ⇒ B) rewrite substᵗ-comp σ τ A | substᵗ-comp σ τ B = refl
substᵗ-comp σ τ (∀̇ A) rewrite substᵗ-comp (extsᵗ σ) (extsᵗ τ) A
  | substᵗ-cong A (extsᵗ-substᵗ σ τ) = refl

σ₀ᵗ-extᵗ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') (B : Type Δ) (x : TyVar (Δ ,α))
  → renameᵗ ρ (σ₀ᵗ B x) ≡ σ₀ᵗ (renameᵗ ρ B) (extᵗ ρ x)
σ₀ᵗ-extᵗ ρ B Z      = refl
σ₀ᵗ-extᵗ ρ B (S x)  = refl

renameᵗ-[]ᵗ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') (A : Type (Δ ,α)) (B : Type Δ)
  → renameᵗ ρ (A [ B ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ renameᵗ ρ B ]ᵗ
renameᵗ-[]ᵗ ρ A B
  rewrite renameᵗ-substᵗ ρ (σ₀ᵗ B) A
        | substᵗ-cong A (σ₀ᵗ-extᵗ ρ B)
        | substᵗ-renameᵗ (extᵗ ρ) (σ₀ᵗ (renameᵗ ρ B)) A = refl

substᵗ-id : ∀ {Δ} (A : Type Δ) → substᵗ (`_) A ≡ A
substᵗ-id (` x)    = refl
substᵗ-id `Nat     = refl
substᵗ-id (A ⇒ B)  rewrite substᵗ-id A | substᵗ-id B = refl
substᵗ-id (∀̇ A) = cong ∀̇_ eq
  where
  exts-id : ∀ α → extsᵗ (`_) α ≡ ` α
  exts-id Z      = refl
  exts-id (S _)  = refl
  eq : substᵗ (extsᵗ (`_)) A ≡ A
  eq rewrite substᵗ-cong A exts-id | substᵗ-id A = refl

[]ᵗ-cancel-shift : ∀ {Δ} (A : Type Δ) (B : Type Δ) → (⇑ᵗ A) [ B ]ᵗ ≡ A
[]ᵗ-cancel-shift A B rewrite substᵗ-renameᵗ S_ (σ₀ᵗ B) A | substᵗ-id A = refl

substᵗ-σ₀ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') (B : Type Δ) (x : TyVar (Δ ,α))
  → substᵗ σ (σ₀ᵗ B x) ≡ substᵗ (σ₀ᵗ (substᵗ σ B)) (extsᵗ σ x)
substᵗ-σ₀ σ B Z      = refl
substᵗ-σ₀ σ B (S x)  = sym ([]ᵗ-cancel-shift (σ x) (substᵗ σ B))

substᵗ-[]ᵗ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') (A : Type (Δ ,α)) (B : Type Δ)
  → substᵗ σ (A [ B ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ substᵗ σ B ]ᵗ
substᵗ-[]ᵗ σ A B
  rewrite substᵗ-comp (σ₀ᵗ B) σ A
        | substᵗ-cong A (substᵗ-σ₀ σ B)
        | sym (substᵗ-comp (extsᵗ σ) (σ₀ᵗ (substᵗ σ B)) A) = refl

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

substCtx-extsᵗ-⇑ᶜ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') (Γ : Ctx Δ)
  → substCtx (extsᵗ σ) (⇑ᶜ Γ) ≡ ⇑ᶜ (substCtx σ Γ)
substCtx-extsᵗ-⇑ᶜ σ ∅ = refl
substCtx-extsᵗ-⇑ᶜ σ (Γ , A) rewrite substCtx-extsᵗ-⇑ᶜ σ Γ | substᵗ-shift σ A = refl

⇑ᵗ-∋ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
  → Γ ∋ A
  → ⇑ᶜ Γ ∋ ⇑ᵗ A
⇑ᵗ-∋ = renameᵗ-∋ S_

-----------------------------------
-- | Intrinsically typed terms | --
-----------------------------------

data _;_⊢_ (Δ : TyCtx) (Γ : Ctx Δ) : Type Δ → Set where

  `zero :
      ---------------
    Δ ; Γ ⊢ `Nat

  `_ : ∀ {A}
    → Γ ∋ A
      ---------------
    → Δ ; Γ ⊢ A

  ƛ_˙_ : ∀ {B}
    → (A : Type Δ)
    → Δ ; Γ , A ⊢ B
      ---------------
    → Δ ; Γ ⊢ A ⇒ B

  _·_ : ∀ {A B}
    → Δ ; Γ ⊢ A ⇒ B
    → Δ ; Γ ⊢ A
      ------------------
    → Δ ; Γ ⊢ B

  Λ_ : ∀ {A}
    → Δ ,α ; ⇑ᶜ Γ ⊢ A
      ------------------
    → Δ ; Γ ⊢ ∀̇ A

  _∙_    : ∀ {A}
    → Δ ; Γ ⊢ (∀̇ A)
    → (B : Type Δ)
      ------------------
    → Δ ; Γ ⊢ A [ B ]ᵗ


------------------------------------
-- | Substitute types into term | --
------------------------------------

renameCtx-extᵗ-⇑ᶜ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') (Γ : Ctx Δ)
  → renameCtx (extᵗ ρ) (⇑ᶜ Γ) ≡ ⇑ᶜ (renameCtx ρ Γ)
renameCtx-extᵗ-⇑ᶜ ρ ∅ = refl
renameCtx-extᵗ-⇑ᶜ ρ (Γ , A)
  rewrite renameCtx-extᵗ-⇑ᶜ ρ Γ | renameᵗ-shift ρ A = refl

renameᵀ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') {Γ : Ctx Δ} {A : Type Δ}
  → Δ ; Γ ⊢ A
  → Δ' ; renameCtx ρ Γ ⊢ renameᵗ ρ A
renameᵀ ρ `zero    = `zero
renameᵀ ρ (` x)    = ` (renameᵗ-∋ ρ x)
renameᵀ ρ (ƛ _ ˙ N)    = ƛ _ ˙ (renameᵀ ρ N)
renameᵀ ρ (L · M)  = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ {Γ = Γ} (Λ N) = Λ (substEq (_ ;_⊢ _) (renameCtx-extᵗ-⇑ᶜ ρ Γ) (renameᵀ (extᵗ ρ) N))
renameᵀ ρ {Γ = Γ} (_∙_ {A = A} M B) rewrite renameᵗ-[]ᵗ ρ A B = renameᵀ ρ M ∙ renameᵗ ρ B

⇑ᵀ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
  → Δ ; Γ ⊢ A
  → Δ ,α ; ⇑ᶜ Γ ⊢ renameᵗ S_ A
⇑ᵀ = renameᵀ S_

substᵀ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') {Γ : Ctx Δ} {A : Type Δ}
  → Δ ; Γ ⊢ A
  → Δ' ; substCtx σ Γ ⊢ substᵗ σ A
substᵀ σ `zero    = `zero
substᵀ σ (` x)    = ` (substᵗ-∋ σ x)
substᵀ σ (ƛ _ ˙ N)    = ƛ _ ˙ (substᵀ σ N)
substᵀ σ (L · M)  = substᵀ σ L · substᵀ σ M
substᵀ σ {Γ = Γ} (Λ N) = Λ (substEq (_ ;_⊢ _) (substCtx-extsᵗ-⇑ᶜ σ Γ) (substᵀ (extsᵗ σ) N))
substᵀ σ (_∙_ {A = A} M B) rewrite substᵗ-[]ᵗ σ A B = substᵀ σ M ∙ substᵗ σ B

substCtx-σ₀-⇑ᶜ-cancel : ∀ {Δ} (Γ : Ctx Δ) (B : Type Δ)
  → substCtx (σ₀ᵗ B) (⇑ᶜ Γ) ≡ Γ
substCtx-σ₀-⇑ᶜ-cancel ∅ B = refl
substCtx-σ₀-⇑ᶜ-cancel (Γ , A) B rewrite substCtx-σ₀-⇑ᶜ-cancel Γ B
  | []ᵗ-cancel-shift A B = refl

_[_]ᵀ : ∀ {Δ} {Γ : Ctx Δ} {A : Type (Δ ,α)}
  → Δ ,α ; ⇑ᶜ Γ ⊢ A
  → (B : Type Δ)
  → Δ ; Γ ⊢ A [ B ]ᵗ
_[_]ᵀ {Γ = Γ} {A = A} N B =
  substEq (_ ;_⊢ A [ B ]ᵗ) (substCtx-σ₀-⇑ᶜ-cancel Γ B) (substᵀ (σ₀ᵗ B) N)



------------------------------------
-- | Substitute terms into term | --
------------------------------------

_→ʳ_ : ∀ {Δ} → Ctx Δ → Ctx Δ → Set
_→ʳ_ Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

ext : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  → Γ →ʳ Γ'
  → (Γ , A) →ʳ (Γ' , A)
ext ρ Z      = Z
ext ρ (S x)  = S (ρ x)

⇑ʳ : ∀ {Δ} {Γ Γ' : Ctx Δ}
  → Γ →ʳ Γ'
  → (⇑ᶜ Γ) →ʳ (⇑ᶜ Γ')
⇑ʳ {Γ = ∅}     ρ ()
⇑ʳ {Γ = Γ , A} ρ Z      = ⇑ᵗ-∋ (ρ Z)
⇑ʳ {Γ = Γ , A} ρ (S x)  = ⇑ʳ (λ y → ρ (S y)) x

rename : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  → Γ →ʳ Γ'
  → Δ ; Γ ⊢ A
  → Δ ; Γ' ⊢ A
rename ρ `zero    = `zero
rename ρ (` x)    = ` (ρ x)
rename ρ (ƛ _ ˙ N)    = ƛ _ ˙ (rename (ext ρ) N)
rename ρ (L · M)  = rename ρ L · rename ρ M
rename ρ (Λ N)    = Λ (rename (⇑ʳ ρ) N)
rename ρ (M ∙ B)  = rename ρ M ∙ B

_→ˢ_ : ∀ {Δ} → Ctx Δ → Ctx Δ → Set
_→ˢ_ Γ Γ' = ∀ {A} → Γ ∋ A → _ ; Γ' ⊢ A

⇑ : ∀ {Δ} {Γ : Ctx Δ} {A B : Type Δ}
  → Δ ; Γ ⊢ A
  → Δ ; Γ , B ⊢ A
⇑ M = rename S_ M

exts : ∀ {Δ} {Γ Δ' : Ctx Δ} {A : Type Δ}
  → Γ →ˢ Δ'
  → (Γ , A) →ˢ (Δ' , A)
exts σ Z      = ` Z
exts σ (S x)  = ⇑ (σ x)

⇑ˢ : ∀ {Δ} {Γ Δ' : Ctx Δ}
  → Γ →ˢ Δ'
  → (⇑ᶜ Γ) →ˢ (⇑ᶜ Δ')
⇑ˢ {Γ = ∅} σ ()
⇑ˢ {Γ = Γ , A} σ Z       = ⇑ᵀ (σ Z)
⇑ˢ {Γ = Γ , A} σ (S x)   = ⇑ˢ (λ y → σ (S y)) x

subst : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  → Γ →ˢ Γ'
  → Δ ; Γ ⊢ A
  → Δ ; Γ' ⊢ A
subst σ `zero    = `zero
subst σ (` x)    = σ x
subst σ (ƛ A ˙ N)    = ƛ A ˙ (subst (exts σ) N)
subst σ (L · M)  = subst σ L · subst σ M
subst σ (Λ N)    = Λ (subst (⇑ˢ σ) N)
subst σ (M ∙ B)  = subst σ M ∙ B

σ₀ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
  → Δ ; Γ ⊢ A
  → (Γ , A) →ˢ Γ
σ₀ M Z      = M
σ₀ M (S x)  = ` x

_[_] : ∀ {Δ} {Γ : Ctx Δ} {A B : Type Δ}
  → Δ ; Γ , A ⊢ B
  → Δ ; Γ ⊢ A
  → Δ ; Γ ⊢ B
_[_] N M = subst (σ₀ M) N



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

  ξ-∙ : ∀ {Δ Γ A B} {M M′ : Δ ; Γ ⊢ ∀̇ A}
    →     M —→ M′
      ---------------------------------------
    → M ∙ B —→ M′ ∙ B

  β-ƛ : ∀ {Δ Γ A B} {N : Δ ; Γ , A ⊢ B} {W}
    →          Value W
      ------------------------------
    → (ƛ A ˙ N) · W —→ N [ W ]

  β-Λ : ∀ {Δ Γ A B} {N : Δ ,α ; ⇑ᶜ Γ ⊢ A}
      ---------------------------------------
    → (Λ N) ∙ B —→ N [ B ]ᵀ

------------------
-- | Progress | --
------------------

{- TBA -}
