{-# OPTIONS --rewriting #-}

open import LambdaSec.LabelLattice using (LabelLattice; extensionality; cong₃)

module LambdaSec.LambdaSec (𝑳 : LabelLattice) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Function using (case_of_)

-- Need the following two imports for rewriting
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite


open LabelLattice 𝑳 public

infix 4 _⊑_ _⊑?_

_⊑_ : ℒ → ℒ → Set
ℓ₁ ⊑ ℓ₂ = ℓ₁ ⊔ ℓ₂ ≡ ℓ₂

_⊑?_ : ∀ (ℓ₁ ℓ₂ : ℒ) → Dec (ℓ₁ ⊑ ℓ₂)
ℓ₁ ⊑? ℓ₂ = (ℓ₁ ⊔ ℓ₂) ≟ₗ ℓ₂

⊑-refl : ∀ {ℓ} → ℓ ⊑ ℓ
⊑-refl = ⊔-idem

⊑-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} → ℓ₁ ⊑ ℓ₂ → ℓ₂ ⊑ ℓ₃ → ℓ₁ ⊑ ℓ₃
⊑-trans {ℓ₁} {ℓ₂} {ℓ₃} ℓ₁⊑ℓ₂ ℓ₂⊑ℓ₃ =
  trans (cong (ℓ₁ ⊔_) (sym ℓ₂⊑ℓ₃))
        (trans (sym ⊔-assoc) (trans (cong (_⊔ ℓ₃) ℓ₁⊑ℓ₂) ℓ₂⊑ℓ₃))

⊑-antisym : ∀ {ℓ₁ ℓ₂} → ℓ₁ ⊑ ℓ₂ → ℓ₂ ⊑ ℓ₁ → ℓ₁ ≡ ℓ₂
⊑-antisym {ℓ₁} {ℓ₂} ℓ₁⊑ℓ₂ ℓ₂⊑ℓ₁ = trans (sym ℓ₂⊑ℓ₁) (trans ⊔-comm ℓ₁⊑ℓ₂)

⊥ₗ-least : ∀ {ℓ} → ⊥ₗ ⊑ ℓ
⊥ₗ-least = ⊥ₗ-identity

⊔-upper₁ : ∀ {ℓ₁ ℓ₂} → ℓ₁ ⊑ (ℓ₁ ⊔ ℓ₂)
⊔-upper₁ {ℓ₁} {ℓ₂} = trans (sym ⊔-assoc) (cong (_⊔ ℓ₂) ⊔-idem)

⊔-upper₂ : ∀ {ℓ₁ ℓ₂} → ℓ₂ ⊑ (ℓ₁ ⊔ ℓ₂)
⊔-upper₂ {ℓ₁} {ℓ₂} =
  trans (sym ⊔-assoc)
        (trans (cong (_⊔ ℓ₂) ⊔-comm) (trans ⊔-assoc (cong (ℓ₁ ⊔_) ⊔-idem)))

⊔-least : ∀ {ℓ₁ ℓ₂ ℓ₃} → ℓ₁ ⊑ ℓ₃ → ℓ₂ ⊑ ℓ₃ → (ℓ₁ ⊔ ℓ₂) ⊑ ℓ₃
⊔-least {ℓ₁} {ℓ₂} {ℓ₃} ℓ₁⊑ℓ₃ ℓ₂⊑ℓ₃ =
  trans ⊔-assoc (trans (cong (ℓ₁ ⊔_) ℓ₂⊑ℓ₃) ℓ₁⊑ℓ₃)

infix  4 _⊢ᵛ_
infix  4 _⊢ᵉ_
infix  4 _∋_
infixl 5 _,_

infixr 6 _⇒_
infix  7 _of_

infix  5 ƛ_of_
infix  6 if_then_else_
infixl 7 _·_
infixl 8 _`∧_
infixl 8 _`∨_
infix  9 val_
infix  9 $_of_
infix  9 `_
infix  9 S_

data Type : Set; data SecType : Set

-- | Plain types
data Type where
  `𝔹   : Type
  _⇒_ : SecType → SecType → Type

-- | Security types
data SecType where
  _of_ : Type → ℒ → SecType

-- | Typing context is standard
data Context : Set where
  ∅   : Context
  _,_ : Context → SecType → Context

data _∋_ : Context → SecType → Set where

  Z : ∀ {Γ A}
      ------------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ------------
    → Γ , B ∋ A

-- | Label stamping on types
stamp : SecType → ℒ → SecType
stamp (T of ℓ₁) ℓ₂ = T of (ℓ₁ ⊔ ℓ₂)

-- | Subtyping
data _<:ₜ_ : Type → Type → Set
data _<:ₛ_ : SecType → SecType → Set

data _<:ₜ_ where

    <:-𝔹 : `𝔹 <:ₜ `𝔹

    <:-⇒ : ∀ {A B C D}
      → C <:ₛ A
      → B <:ₛ D
        ------------------------
      → (A ⇒ B) <:ₜ (C ⇒ D)

data _<:ₛ_ where

    <:-lab : ∀ {S T ℓ₁ ℓ₂}
      → S <:ₜ T
      → ℓ₁ ⊑ ℓ₂
        ---------------------------
      → (S of ℓ₁) <:ₛ (T of ℓ₂)

-- | Typing rules
data _⊢ᵛ_ : Context → SecType → Set
data _⊢ᵉ_ : Context → SecType → Set

data _⊢ᵛ_ where

  $_of_ : ∀ {Γ}
    → (b : Bool)
    → (ℓ : ℒ)
      ------------------- (Tv-Bool)
    → Γ ⊢ᵛ `𝔹 of ℓ

  ƛ_of_  : ∀ {Γ A B}
    → (Γ , A) ⊢ᵉ B
    → (ℓ : ℒ)
      ------------------------ (Tv-Abs)
    → Γ ⊢ᵛ (A ⇒ B) of ℓ

stamp-val : ∀ {Γ A} → Γ ⊢ᵛ A → (ℓ : ℒ) → Γ ⊢ᵛ (stamp A ℓ)
stamp-val ($ b of ℓ₁) ℓ₂ = $ b of (ℓ₁ ⊔ ℓ₂)
stamp-val (ƛ N of ℓ₁) ℓ₂ = ƛ N of (ℓ₁ ⊔ ℓ₂)

data _⊢ᵉ_ where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      ------------ (T-Var)
    → Γ ⊢ᵉ A

  val_ : ∀ {Γ A}
    → Γ ⊢ᵛ A
      ------------ (T-Val)
    → Γ ⊢ᵉ A

  _`∧_ : ∀ {Γ ℓ₁ ℓ₂}
    → Γ ⊢ᵉ `𝔹 of ℓ₁
    → Γ ⊢ᵉ `𝔹 of ℓ₂
      ------------------------ (T-And)
    → Γ ⊢ᵉ `𝔹 of (ℓ₁ ⊔ ℓ₂)

  _`∨_ : ∀ {Γ ℓ₁ ℓ₂}
    → Γ ⊢ᵉ `𝔹 of ℓ₁
    → Γ ⊢ᵉ `𝔹 of ℓ₂
      ------------------------ (T-Or)
    → Γ ⊢ᵉ `𝔹 of (ℓ₁ ⊔ ℓ₂)

  _·_ : ∀ {Γ S T ℓ₁ ℓ₂ ℓ₃}
    → Γ ⊢ᵉ (S of ℓ₁ ⇒ T of ℓ₂) of ℓ₃
    → Γ ⊢ᵉ S of ℓ₁
      ------------------------------------ (T-App)
    → Γ ⊢ᵉ T of (ℓ₂ ⊔ ℓ₃)

  if_then_else_ : ∀ {Γ T ℓ₁ ℓ₂}
    → Γ ⊢ᵉ `𝔹 of ℓ₁
    → Γ ⊢ᵉ T of (ℓ₂ ⊔ ℓ₁)
    → Γ ⊢ᵉ T of (ℓ₂ ⊔ ℓ₁)
      --------------------------- (T-If)
    → Γ ⊢ᵉ T of (ℓ₂ ⊔ ℓ₁)

  sub : ∀ {Γ A B}
    → Γ ⊢ᵉ A
    → A <:ₛ B
      --------------- (T-Subsumption)
    → Γ ⊢ᵉ B

-- | Substitution and substitution lemmas
_→ʳ_ _→ˢ_ : Context → Context → Set
Γ →ʳ Δ = ∀ {X} → Γ ∋ X → Δ ∋ X
Γ →ˢ Δ = ∀ {X} → Γ ∋ X → Δ ⊢ᵉ X

infixr 6 _•ʳ_
_•ʳ_ : ∀ {Γ Δ A} → Δ ∋ A → Γ →ʳ Δ → (Γ , A) →ʳ Δ
(x •ʳ ρ) Z      = x
(x •ʳ ρ) (S y)  = ρ y

⇑ʳ : ∀ {Γ Δ A} → Γ →ʳ Δ → Γ →ʳ (Δ , A)
⇑ʳ ρ x = S (ρ x)

idʳ : ∀ {Γ} → Γ →ʳ Γ
idʳ x = x

Z-shiftʳ : ∀ {Γ A B} → (Z •ʳ ⇑ʳ idʳ) ≡ idʳ {Γ , A} {B}
Z-shiftʳ = extensionality λ where
  Z      → refl
  (S x)  → refl
{-# REWRITE Z-shiftʳ #-}

ext : ∀ {Γ Δ A} → Γ →ʳ Δ → (Γ , A) →ʳ (Δ , A)
ext ρ = Z •ʳ ⇑ʳ ρ

renameᵛ : ∀ {Γ Δ A} → Γ →ʳ Δ → Γ ⊢ᵛ A → Δ ⊢ᵛ A
renameᵉ : ∀ {Γ Δ A} → Γ →ʳ Δ → Γ ⊢ᵉ A → Δ ⊢ᵉ A
renameᵛ ρ (ƛ N of ℓ)           = ƛ renameᵉ (ext ρ) N of ℓ
renameᵛ ρ ($ b of ℓ)      = $ b of ℓ
renameᵉ ρ (` x)                =  ` ρ x
renameᵉ ρ (val v)              =  val (renameᵛ ρ v)
renameᵉ ρ (L · M)              =  renameᵉ ρ L · renameᵉ ρ M
renameᵉ ρ (if L then M else N) =  if renameᵉ ρ L then renameᵉ ρ M else renameᵉ ρ N
renameᵉ ρ (M `∧ N)             =  renameᵉ ρ M `∧ renameᵉ ρ N
renameᵉ ρ (M `∨ N)             =  renameᵉ ρ M `∨ renameᵉ ρ N
renameᵉ ρ (sub M A<:B)         =  sub (renameᵉ ρ M) A<:B

id : ∀ {Γ} → Γ →ˢ Γ
id x = ` x

↑ : ∀ {Γ A} → Γ →ˢ (Γ , A)
↑ x = ` (S x)

_•_ : ∀ {Γ Δ A} → Δ ⊢ᵉ A → Γ →ˢ Δ → (Γ , A) →ˢ Δ
(M • σ) Z = M
(M • σ) (S x) = σ x

⇑ : ∀ {Γ Δ A} → Γ →ˢ Δ → Γ →ˢ (Δ , A)
⇑ σ x = renameᵉ S_ (σ x)

exts : ∀ {Γ Δ A} → Γ →ˢ Δ → (Γ , A) →ˢ (Δ , A)
exts σ = (` Z) • ⇑ σ

ren : ∀ {Γ Δ} → Γ →ʳ Δ → Γ →ˢ Δ
ren ρ x = ` ρ x

substᵛ : ∀ {Γ Δ A} → Γ →ˢ Δ → Γ ⊢ᵛ A → Δ ⊢ᵛ A
substᵉ : ∀ {Γ Δ A} → Γ →ˢ Δ → Γ ⊢ᵉ A → Δ ⊢ᵉ A
substᵛ σ (ƛ N of ℓ)           = ƛ substᵉ (exts σ) N of ℓ
substᵛ σ ($ b of ℓ)      = $ b of ℓ
substᵉ σ (` x)                = σ x
substᵉ σ (val v)              = val (substᵛ σ v)
substᵉ σ (L · M)              = substᵉ σ L · substᵉ σ M
substᵉ σ (if L then M else N) = if substᵉ σ L then substᵉ σ M else substᵉ σ N
substᵉ σ (M `∧ N)             = substᵉ σ M `∧ substᵉ σ N
substᵉ σ (M `∨ N)             = substᵉ σ M `∨ substᵉ σ N
substᵉ σ (sub M A<:B)         = sub (substᵉ σ M) A<:B

_[_] : ∀ {Γ A B} → Γ , A ⊢ᵉ B → Γ ⊢ᵉ A → Γ ⊢ᵉ B
N [ M ] =  substᵉ (M • id) N

abstract
  infixr 5 _⨟_
  _⨟_ : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ →ˢ Γ₂ → Γ₂ →ˢ Γ₃ → Γ₁ →ˢ Γ₃
  σ₁ ⨟ σ₂ = λ x → substᵉ σ₂ (σ₁ x)

  seq-def : ∀ {Γ₁ Γ₂ Γ₃ A} (σ₁ : Γ₁ →ˢ Γ₂) (σ₂ : Γ₂ →ˢ Γ₃) (x : Γ₁ ∋ A)
    → (σ₁ ⨟ σ₂) x ≡ substᵉ σ₂ (σ₁ x)
  seq-def σ₁ σ₂ x = refl
{-# REWRITE seq-def #-}

sub-dist : ∀ {Γ Δ Ψ A B} (M : Δ ⊢ᵉ A) (σ : Γ →ˢ Δ) (τ : Δ →ˢ Ψ)
  → ((M • σ) ⨟ τ) {B} ≡ (substᵉ τ M) • (σ ⨟ τ)
sub-dist M σ τ = extensionality λ where
  Z → refl
  (S x) → refl
{-# REWRITE sub-dist #-}

exts-ren : ∀ {Γ Δ A B} (ρ : Γ →ʳ Δ)
  → ((` Z) • ⇑ (ren ρ)) {B} ≡ ren ((Z {A = A}) •ʳ ⇑ʳ ρ)
exts-ren ρ = extensionality λ where
  Z      → refl
  (S x)  → refl
{-# REWRITE exts-ren #-}

sub-idᵛ : ∀ {Γ A} (V : Γ ⊢ᵛ A) → substᵛ id V ≡ V
sub-id  : ∀ {Γ A} (M : Γ ⊢ᵉ A) → substᵉ id M ≡ M
sub-idᵛ (ƛ N of ℓ) = cong (λ □ → ƛ □ of ℓ) (sub-id N)
sub-idᵛ ($ b of ℓ) = refl
sub-id (` x) = refl
sub-id (val V) = cong val_ (sub-idᵛ V)
sub-id (L · M) = cong₂ _·_ (sub-id L) (sub-id M)
sub-id (if L then M else N) = cong₃ if_then_else_ (sub-id L) (sub-id M) (sub-id N)
sub-id (M `∧ N) = cong₂ _`∧_ (sub-id M) (sub-id N)
sub-id (M `∨ N) = cong₂ _`∨_ (sub-id M) (sub-id N)
sub-id (sub M A<:B) = cong (λ M′ → sub M′ A<:B) (sub-id M)
{-# REWRITE sub-id #-}

rename-subst-renᵛ : ∀ {Γ Δ A} (ρ : Γ →ʳ Δ) (V : Γ ⊢ᵛ A)
    → renameᵛ ρ V ≡ substᵛ (ren ρ) V
rename-subst-renᵉ : ∀ {Γ Δ A} (ρ : Γ →ʳ Δ) (M : Γ ⊢ᵉ A)
    → renameᵉ ρ M ≡ substᵉ (ren ρ) M
rename-subst-renᵛ ρ (ƛ N of ℓ) =
    cong (λ N′ → ƛ N′ of ℓ) (rename-subst-renᵉ (ext ρ) N)
rename-subst-renᵛ ρ ($ b of ℓ) = refl
rename-subst-renᵉ ρ (` x) = refl
rename-subst-renᵉ ρ (val V) = cong val_ (rename-subst-renᵛ ρ V)
rename-subst-renᵉ ρ (L · M) = cong₂ _·_ (rename-subst-renᵉ ρ L) (rename-subst-renᵉ ρ M)
rename-subst-renᵉ ρ (if L then M else N) =
  cong₃ if_then_else_ (rename-subst-renᵉ ρ L) (rename-subst-renᵉ ρ M) (rename-subst-renᵉ ρ N)
rename-subst-renᵉ ρ (M `∧ N) = cong₂ _`∧_ (rename-subst-renᵉ ρ M) (rename-subst-renᵉ ρ N)
rename-subst-renᵉ ρ (M `∨ N) = cong₂ _`∨_ (rename-subst-renᵉ ρ M) (rename-subst-renᵉ ρ N)
rename-subst-renᵉ ρ (sub M A<:B) = cong (λ M′ → sub M′ A<:B) (rename-subst-renᵉ ρ M)
{-# REWRITE rename-subst-renᵉ #-}

ext-ren-sub : ∀ {Γ Δ Ψ A B} (ρ : Γ →ʳ Δ) (σ : Δ →ˢ Ψ)
  → (exts (ren ρ) ⨟ exts σ) {B} ≡ exts {A = A} (ren ρ ⨟ σ)
ext-ren-sub ρ _ = extensionality λ where
  Z      → refl
  (S x)  → refl
{-# REWRITE ext-ren-sub #-}

ren-subᵛ : ∀ {Γ Δ Ψ A} (ρ : Γ →ʳ Δ) (τ : Δ →ˢ Ψ) (V : Γ ⊢ᵛ A)
    → substᵛ τ (substᵛ (ren ρ) V) ≡ substᵛ (ren ρ ⨟ τ) V
ren-subᵉ : ∀ {Γ Δ Ψ A} (ρ : Γ →ʳ Δ) (τ : Δ →ˢ Ψ) (M : Γ ⊢ᵉ A)
    → substᵉ τ (substᵉ (ren ρ) M) ≡ substᵉ (ren ρ ⨟ τ) M
ren-subᵛ ρ τ (ƛ N of ℓ) = cong (ƛ_of ℓ) (ren-subᵉ (ext ρ) (exts τ) N)
ren-subᵛ ρ τ ($ b of ℓ) = refl
ren-subᵉ ρ τ (` x) = refl
ren-subᵉ ρ τ (val V) = cong val_ (ren-subᵛ ρ τ V)
ren-subᵉ ρ τ (L · M) = cong₂ _·_ (ren-subᵉ ρ τ L) (ren-subᵉ ρ τ M)
ren-subᵉ ρ τ (if L then M else N) =
  cong₃ if_then_else_ (ren-subᵉ ρ τ L) (ren-subᵉ ρ τ M) (ren-subᵉ ρ τ N)
ren-subᵉ ρ τ (M `∧ N) = cong₂ _`∧_ (ren-subᵉ ρ τ M) (ren-subᵉ ρ τ N)
ren-subᵉ ρ τ (M `∨ N) = cong₂ _`∨_ (ren-subᵉ ρ τ M) (ren-subᵉ ρ τ N)
ren-subᵉ ρ τ (sub M A<:B) = cong (λ □ → sub □ A<:B) (ren-subᵉ ρ τ M)
{-# REWRITE ren-subᵉ #-}

sub-renᵛ : ∀ {Γ Δ Ψ A} (σ : Γ →ˢ Δ) (ρ : Δ →ʳ Ψ) (V : Γ ⊢ᵛ A)
    → substᵛ (ren ρ) (substᵛ σ V) ≡ substᵛ (σ ⨟ ren ρ) V
sub-renᵉ : ∀ {Γ Δ Ψ A} (σ : Γ →ˢ Δ) (ρ : Δ →ʳ Ψ) (M : Γ ⊢ᵉ A)
    → substᵉ (ren ρ) (substᵉ σ M) ≡ substᵉ (σ ⨟ ren ρ) M
sub-renᵛ σ ρ (ƛ N of ℓ) = cong (ƛ_of ℓ) (sub-renᵉ (exts σ) (ext ρ) N)
sub-renᵛ σ ρ ($ b of ℓ) = refl
sub-renᵉ σ ρ (` x) = refl
sub-renᵉ σ ρ (val V) = cong val_ (sub-renᵛ σ ρ V)
sub-renᵉ σ ρ (L · M) = cong₂ _·_ (sub-renᵉ σ ρ L) (sub-renᵉ σ ρ M)
sub-renᵉ σ ρ (if L then M else N) =
  cong₃ if_then_else_ (sub-renᵉ σ ρ L) (sub-renᵉ σ ρ M) (sub-renᵉ σ ρ N)
sub-renᵉ σ ρ (M `∧ N) = cong₂ _`∧_ (sub-renᵉ σ ρ M) (sub-renᵉ σ ρ N)
sub-renᵉ σ ρ (M `∨ N) = cong₂ _`∨_ (sub-renᵉ σ ρ M) (sub-renᵉ σ ρ N)
sub-renᵉ σ ρ (sub M A<:B) = cong (λ M′ → sub M′ A<:B) (sub-renᵉ σ ρ M)
{-# REWRITE sub-renᵉ #-}

sub-subᵛ : ∀ {Γ Δ Ψ A} (σ : Γ →ˢ Δ) (τ : Δ →ˢ Ψ) (V : Γ ⊢ᵛ A)
    → substᵛ τ (substᵛ σ V) ≡ substᵛ (σ ⨟ τ) V
sub-sub : ∀ {Γ Δ Ψ A} (σ : Γ →ˢ Δ) (τ : Δ →ˢ Ψ) (M : Γ ⊢ᵉ A)
    → substᵉ τ (substᵉ σ M) ≡ substᵉ (σ ⨟ τ) M
sub-subᵛ {Γ = Γ} σ τ (ƛ N of ℓ) = cong (ƛ_of ℓ) (sub-sub (exts σ) (exts τ) N)
sub-subᵛ σ τ ($ b of ℓ) = refl
sub-sub σ τ (` x) = refl
sub-sub σ τ (val V) = cong val_ (sub-subᵛ σ τ V)
sub-sub σ τ (L · M) = cong₂ _·_ (sub-sub σ τ L) (sub-sub σ τ M)
sub-sub σ τ (if L then M else N) =
  cong₃ if_then_else_ (sub-sub σ τ L) (sub-sub σ τ M) (sub-sub σ τ N)
sub-sub σ τ (M `∧ N) = cong₂ _`∧_ (sub-sub σ τ M) (sub-sub σ τ N)
sub-sub σ τ (M `∨ N) = cong₂ _`∨_ (sub-sub σ τ M) (sub-sub σ τ N)
sub-sub σ τ (sub M A<:B) = cong (λ M′ → sub M′ A<:B) (sub-sub σ τ M)
{-# REWRITE sub-sub #-}

exts-sub-cons : ∀ {Γ Δ A B} (σ : Γ →ˢ Δ) (N : Γ , B ⊢ᵉ A) (M : Δ ⊢ᵉ B)
    ------------------------------------------------------------------------
  → (substᵉ (exts σ) N) [ M ] ≡ substᵉ (M • σ) N
exts-sub-cons σ N M = refl


-- | Big-step operational semantics
infix 1 _⟦∧⟧_ _⟦∨⟧_

_⟦∧⟧_ _⟦∨⟧_ : ∀ {ℓ₁ ℓ₂} → ∅ ⊢ᵛ `𝔹 of ℓ₁ → ∅ ⊢ᵛ `𝔹 of ℓ₂ → ∅ ⊢ᵛ `𝔹 of _
($ b₁ of ℓ₁) ⟦∧⟧ ($ b₂ of ℓ₂) = $ (b₁ ∧ b₂) of (ℓ₁ ⊔ ℓ₂)
($ b₁ of ℓ₁) ⟦∨⟧ ($ b₂ of ℓ₂) = $ (b₁ ∨ b₂) of (ℓ₁ ⊔ ℓ₂)

infix 0 _⇓_

data _⇓_ : ∀ {A} → ∅ ⊢ᵉ A → ∅ ⊢ᵛ A → Set where

  ⇓-val : ∀ {A} {V : ∅ ⊢ᵛ A}
      ---------------------------
    → val V ⇓ V

  ⇓-∧ : ∀ {ℓ₁ ℓ₂ V W}
           {M : ∅ ⊢ᵉ `𝔹 of ℓ₁}
           {N : ∅ ⊢ᵉ `𝔹 of ℓ₂}
     → M ⇓ V
     → N ⇓ W
       ------------------------
     → M `∧ N ⇓ V ⟦∧⟧ W

  ⇓-∨ : ∀ {ℓ₁ ℓ₂ V W}
           {M : ∅ ⊢ᵉ `𝔹 of ℓ₁}
           {N : ∅ ⊢ᵉ `𝔹 of ℓ₂}
     → M ⇓ V
     → N ⇓ W
       ------------------------
     → M `∨ N ⇓ V ⟦∨⟧ W

  ⇓-if-then : ∀ {T ℓₗ ℓ₂ V}
                 {L   : ∅ ⊢ᵉ `𝔹 of ℓₗ}
                 {M N : ∅ ⊢ᵉ T of (ℓ₂ ⊔ ℓₗ)}
    → L ⇓ $ true of ℓₗ
    → M ⇓ V
      ---------------------------------------------
    → if L then M else N ⇓ V

  ⇓-if-else : ∀ {T ℓₗ ℓ₂ V}
                 {L   : ∅ ⊢ᵉ `𝔹 of ℓₗ}
                 {M N : ∅ ⊢ᵉ T of (ℓ₂ ⊔ ℓₗ)}
    → L ⇓ $ false of ℓₗ
    → N ⇓ V
      ---------------------------------------------
    → if L then M else N ⇓ V

  ⇓-app : ∀ {S T ℓ₁ ℓ₂ ℓ₃ W V N}
             {L : ∅ ⊢ᵉ (S of ℓ₁ ⇒ T of ℓ₂) of ℓ₃}
             {M : ∅ ⊢ᵉ S of ℓ₁}
     → L           ⇓ ƛ N of ℓ₃
     → M           ⇓ W
     → N [ val W ] ⇓ V
       ------------------------------------------
     → L · M ⇓ stamp-val V ℓ₃
