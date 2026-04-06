{-# OPTIONS --rewriting #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Function using (case_of_)

-- Need the following two imports for rewriting
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite


-- | The security lattice is a join semilattice with a bottom element (⊥ₗ)
record LabelLattice : Set₁ where

  infixl 6 _⊔_

  field
    ℒ        : Set
    ⊥ₗ       : ℒ
    _⊔_      : ℒ → ℒ → ℒ
    _≟ₗ_     : ∀ (ℓ₁ ℓ₂ : ℒ) → Dec (ℓ₁ ≡ ℓ₂)
    ⊥ₗ-identity : ∀ {ℓ} → ⊥ₗ ⊔ ℓ ≡ ℓ
    ⊔-assoc  : ∀ {ℓ₁ ℓ₂ ℓ₃} → (ℓ₁ ⊔ ℓ₂) ⊔ ℓ₃ ≡ ℓ₁ ⊔ (ℓ₂ ⊔ ℓ₃)
    ⊔-comm   : ∀ {ℓ₁ ℓ₂} → ℓ₁ ⊔ ℓ₂ ≡ ℓ₂ ⊔ ℓ₁
    ⊔-idem   : ∀ {ℓ} → ℓ ⊔ ℓ ≡ ℓ

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ x → f x ≡ g x)
    → f ≡ g

cong₃ : ∀ {A B C D : Set} {x x′ : A} {y y′ : B} {z z′ : C}
  (f : A → B → C → D)
  → x ≡ x′ → y ≡ y′ → z ≡ z′
  → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl


module λSec (𝑳 : LabelLattice) where

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


  -- | Erasure
  infix  6 ifᵉ_then_else_
  infixl 7 _·ᵉ_
  infixl 8 _`∧ᵉ_
  infixl 8 _`∨ᵉ_
  infix  9 $ᵉ_of_
  infix  9 `ᵉ_

  data ErasedTerm : Context → Set where

    ● : ∀ {Γ} → ErasedTerm Γ

    `ᵉ_ : ∀ {Γ A}
      → Γ ∋ A
        ----------------
      → ErasedTerm Γ

    $ᵉ_of_ : ∀ {Γ}
      → Bool
      → ℒ
        ----------------
      → ErasedTerm Γ

    ƛᵉ_of_ : ∀ {Γ A}
      → ErasedTerm (Γ , A)
      → ℒ
        ----------------
      → ErasedTerm Γ

    _`∧ᵉ_ : ∀ {Γ}
      → ErasedTerm Γ
      → ErasedTerm Γ
        ----------------
      → ErasedTerm Γ

    _`∨ᵉ_ : ∀ {Γ}
      → ErasedTerm Γ
      → ErasedTerm Γ
        ----------------
      → ErasedTerm Γ

    _·ᵉ_ : ∀ {Γ}
      → ErasedTerm Γ
      → ErasedTerm Γ
        ----------------
      → ErasedTerm Γ

    ifᵉ_then_else_ : ∀ {Γ}
      → ErasedTerm Γ
      → ErasedTerm Γ
      → ErasedTerm Γ
        ----------------
      → ErasedTerm Γ

  eraseᵛ : ∀ {Γ T ℓ}
      → Γ ⊢ᵛ T of ℓ
      → (ζ : ℒ)
      → Dec (ℓ ⊑ ζ)
        ----------------
      → ErasedTerm Γ
  erase : ∀ {Γ T ℓ}
      → Γ ⊢ᵉ T of ℓ
      → (ζ : ℒ)
      → Dec (ℓ ⊑ ζ)
        ----------------
      → ErasedTerm Γ

  eraseᵛ ($ b of ℓ) ζ (yes _) = $ᵉ b of ℓ
  eraseᵛ ($ b of ℓ) ζ (no  _) = ●
  eraseᵛ (ƛ_of_ {B = T of ℓ′} N ℓ) ζ (yes _) = ƛᵉ erase N ζ (_ ⊑? ζ) of ℓ
  eraseᵛ (ƛ_of_ {B = T of ℓ′} N ℓ) ζ (no  _) = ●

  erase (` x) ζ _ = `ᵉ x
  erase (val V) ζ ℓ⊑ζ? = eraseᵛ V ζ ℓ⊑ζ?
  erase (L `∧ M) ζ _ = erase L ζ (_ ⊑? ζ) `∧ᵉ erase M ζ (_ ⊑? ζ)
  erase (L `∨ M) ζ _ = erase L ζ (_ ⊑? ζ) `∨ᵉ erase M ζ (_ ⊑? ζ)
  erase (L · M) ζ _ = erase L ζ (_ ⊑? ζ) ·ᵉ  erase M ζ (_ ⊑? ζ)
  erase (if L then M else N) ζ _ =
      ifᵉ erase L ζ (_ ⊑? ζ) then erase M ζ (_ ⊑? ζ) else erase N ζ (_ ⊑? ζ)
  erase (sub {A = T₁ of ℓ₁} {T₂ of ℓ₂} M A<:B) ζ (yes _) = erase M ζ (ℓ₁ ⊑? ζ)
  erase (sub {A = T₁ of ℓ₁} {T₂ of ℓ₂} M A<:B) ζ (no  _) = ●

  infix 4 ErasedValue

  data ErasedValue : ∀ {Γ} → ErasedTerm Γ → Set where
    V-● : ∀ {Γ}
        ----------
      → ErasedValue {Γ} ●

    V-$ᵉ : ∀ {Γ b ℓ}
        -----------------
      → ErasedValue {Γ} ($ᵉ b of ℓ)

    V-ƛᵉ : ∀ {Γ A} {N : ErasedTerm (Γ , A)} {ℓ}
        ---------------------
      → ErasedValue {Γ} (ƛᵉ N of ℓ)

  stampₑ : ∀ {Γ} → ErasedTerm Γ → ℒ → ErasedTerm Γ
  stampₑ ●          ℓ = ●
  stampₑ ($ᵉ b of ℓ₁) ℓ₂ = $ᵉ b of (ℓ₁ ⊔ ℓ₂)
  stampₑ (ƛᵉ N of ℓ₁) ℓ₂ = ƛᵉ N of (ℓ₁ ⊔ ℓ₂)
  stampₑ (`ᵉ x)      ℓ = `ᵉ x
  stampₑ (L `∧ᵉ M)   ℓ = stampₑ L ℓ `∧ᵉ stampₑ M ℓ
  stampₑ (L `∨ᵉ M)   ℓ = stampₑ L ℓ `∨ᵉ stampₑ M ℓ
  stampₑ (L ·ᵉ M)    ℓ = stampₑ L ℓ ·ᵉ stampₑ M ℓ
  stampₑ (ifᵉ L then M else N) ℓ = ifᵉ stampₑ L ℓ then stampₑ M ℓ else stampₑ N ℓ

  _→ʳₑ_ _→ˢₑ_ : Context → Context → Set
  Γ →ʳₑ Δ = ∀ {X} → Γ ∋ X → Δ ∋ X
  Γ →ˢₑ Δ = ∀ {X} → Γ ∋ X → ErasedTerm Δ

  infixr 6 _•ʳₑ_
  _•ʳₑ_ : ∀ {Γ Δ A} → Δ ∋ A → Γ →ʳₑ Δ → (Γ , A) →ʳₑ Δ
  (x •ʳₑ ρ) Z     = x
  (x •ʳₑ ρ) (S y) = ρ y

  ⇑ʳₑ : ∀ {Γ Δ A} → Γ →ʳₑ Δ → Γ →ʳₑ (Δ , A)
  ⇑ʳₑ ρ x = S (ρ x)

  extₑ : ∀ {Γ Δ A} → Γ →ʳₑ Δ → (Γ , A) →ʳₑ (Δ , A)
  extₑ ρ = Z •ʳₑ ⇑ʳₑ ρ

  renameₑ : ∀ {Γ Δ} → Γ →ʳₑ Δ → ErasedTerm Γ → ErasedTerm Δ
  renameₑ ρ ● = ●
  renameₑ ρ (`ᵉ x) = `ᵉ ρ x
  renameₑ ρ ($ᵉ b of ℓ) = $ᵉ b of ℓ
  renameₑ ρ (ƛᵉ N of ℓ) = ƛᵉ renameₑ (extₑ ρ) N of ℓ
  renameₑ ρ (L `∧ᵉ M) = renameₑ ρ L `∧ᵉ renameₑ ρ M
  renameₑ ρ (L `∨ᵉ M) = renameₑ ρ L `∨ᵉ renameₑ ρ M
  renameₑ ρ (L ·ᵉ M) = renameₑ ρ L ·ᵉ renameₑ ρ M
  renameₑ ρ (ifᵉ L then M else N) = ifᵉ renameₑ ρ L then renameₑ ρ M else renameₑ ρ N

  renameₑ-cong : ∀ {Γ Δ} {ρ τ : Γ →ʳₑ Δ}
      → (∀ {A} (x : Γ ∋ A) → ρ x ≡ τ x)
      → (M : ErasedTerm Γ)
      → renameₑ ρ M ≡ renameₑ τ M
  renameₑ-cong ρ=τ ● = refl
  renameₑ-cong ρ=τ (`ᵉ x) = cong `ᵉ_ (ρ=τ x)
  renameₑ-cong ρ=τ ($ᵉ b of ℓ) = refl
  renameₑ-cong {ρ = ρ} {τ} ρ=τ (ƛᵉ N of ℓ) =
    cong (ƛᵉ_of ℓ)
         (renameₑ-cong (λ where
                         Z     → refl
                         (S x) → cong S_ (ρ=τ x)) N)
  renameₑ-cong ρ=τ (L `∧ᵉ M) = cong₂ _`∧ᵉ_ (renameₑ-cong ρ=τ L) (renameₑ-cong ρ=τ M)
  renameₑ-cong ρ=τ (L `∨ᵉ M) = cong₂ _`∨ᵉ_ (renameₑ-cong ρ=τ L) (renameₑ-cong ρ=τ M)
  renameₑ-cong ρ=τ (L ·ᵉ M) = cong₂ _·ᵉ_ (renameₑ-cong ρ=τ L) (renameₑ-cong ρ=τ M)
  renameₑ-cong ρ=τ (ifᵉ L then M else N) =
    cong₃ ifᵉ_then_else_ (renameₑ-cong ρ=τ L) (renameₑ-cong ρ=τ M) (renameₑ-cong ρ=τ N)

  idₑ : ∀ {Γ} → Γ →ˢₑ Γ
  idₑ x = `ᵉ x

  ↑ₑ : ∀ {Γ A} → Γ →ˢₑ (Γ , A)
  ↑ₑ x = `ᵉ (S x)

  infixr 6 _•ₑ_
  _•ₑ_ : ∀ {Γ Δ A} → ErasedTerm Δ → Γ →ˢₑ Δ → (Γ , A) →ˢₑ Δ
  (M •ₑ σ) Z = M
  (M •ₑ σ) (S x) = σ x

  ⇑ₑ : ∀ {Γ Δ A} → Γ →ˢₑ Δ → Γ →ˢₑ (Δ , A)
  ⇑ₑ σ x = renameₑ S_ (σ x)

  extsₑ : ∀ {Γ Δ A} → Γ →ˢₑ Δ → (Γ , A) →ˢₑ (Δ , A)
  extsₑ σ = (`ᵉ Z) •ₑ ⇑ₑ σ

  eraseˢ : ∀ {Γ Δ} → Γ →ˢ Δ → ℒ → Γ →ˢₑ Δ
  eraseˢ σ ζ {X = T of ℓ} x = erase (σ x) ζ (ℓ ⊑? ζ)

  substₑ : ∀ {Γ Δ} → Γ →ˢₑ Δ → ErasedTerm Γ → ErasedTerm Δ
  substₑ σ ● = ●
  substₑ σ (`ᵉ x) = σ x
  substₑ σ ($ᵉ b of ℓ) = $ᵉ b of ℓ
  substₑ σ (ƛᵉ N of ℓ) = ƛᵉ substₑ (extsₑ σ) N of ℓ
  substₑ σ (L `∧ᵉ M) = substₑ σ L `∧ᵉ substₑ σ M
  substₑ σ (L `∨ᵉ M) = substₑ σ L `∨ᵉ substₑ σ M
  substₑ σ (L ·ᵉ M) = substₑ σ L ·ᵉ substₑ σ M
  substₑ σ (ifᵉ L then M else N) = ifᵉ substₑ σ L then substₑ σ M else substₑ σ N

  substₑ-cong : ∀ {Γ Δ} {σ τ : Γ →ˢₑ Δ}
      → (∀ {A} (x : Γ ∋ A) → σ x ≡ τ x)
      → (M : ErasedTerm Γ)
      → substₑ σ M ≡ substₑ τ M
  substₑ-cong σ=τ ● = refl
  substₑ-cong σ=τ (`ᵉ x) = σ=τ x
  substₑ-cong σ=τ ($ᵉ b of ℓ) = refl
  substₑ-cong {σ = σ} {τ} σ=τ (ƛᵉ N of ℓ) =
    cong (ƛᵉ_of ℓ) (substₑ-cong exts[σ]=exts[τ] N)
    where
    exts[σ]=exts[τ] : ∀ {A} (x : _ ∋ A) → extsₑ σ x ≡ extsₑ τ x
    exts[σ]=exts[τ] Z     = refl
    exts[σ]=exts[τ] (S x) = cong (renameₑ S_) (σ=τ x)
  substₑ-cong σ=τ (L `∧ᵉ M) = cong₂ _`∧ᵉ_ (substₑ-cong σ=τ L) (substₑ-cong σ=τ M)
  substₑ-cong σ=τ (L `∨ᵉ M) = cong₂ _`∨ᵉ_ (substₑ-cong σ=τ L) (substₑ-cong σ=τ M)
  substₑ-cong σ=τ (L ·ᵉ M) = cong₂ _·ᵉ_ (substₑ-cong σ=τ L) (substₑ-cong σ=τ M)
  substₑ-cong σ=τ (ifᵉ L then M else N) =
    cong₃ ifᵉ_then_else_ (substₑ-cong σ=τ L) (substₑ-cong σ=τ M) (substₑ-cong σ=τ N)

  infix 9 _[_]ₑ
  _[_]ₑ : ∀ {Γ A} → ErasedTerm (Γ , A) → ErasedTerm Γ → ErasedTerm Γ
  N [ M ]ₑ = substₑ (M •ₑ idₑ) N

  infix 1 _⟦∧⟧ₑ_ _⟦∨⟧ₑ_
  _⟦∧⟧ₑ_ _⟦∨⟧ₑ_ : ErasedTerm ∅ → ErasedTerm ∅ → ErasedTerm ∅
  ($ᵉ b₁ of ℓ₁) ⟦∧⟧ₑ ($ᵉ b₂ of ℓ₂) = $ᵉ (b₁ ∧ b₂) of (ℓ₁ ⊔ ℓ₂)
  _              ⟦∧⟧ₑ _              = ●
  ($ᵉ b₁ of ℓ₁) ⟦∨⟧ₑ ($ᵉ b₂ of ℓ₂) = $ᵉ (b₁ ∨ b₂) of (ℓ₁ ⊔ ℓ₂)
  _              ⟦∨⟧ₑ _              = ●

  infix 0 _⇓ₑ_
  data _⇓ₑ_ : ErasedTerm ∅ → ErasedTerm ∅ → Set where

    ⇓ₑ-val : ∀ {V}
      → ErasedValue V
        ----------------
      → V ⇓ₑ V

    ⇓ₑ-∧ : ∀ {L M V W}
      → L ⇓ₑ V
      → M ⇓ₑ W
        ---------------------
      → L `∧ᵉ M ⇓ₑ (V ⟦∧⟧ₑ W)

    ⇓ₑ-∨ : ∀ {L M V W}
      → L ⇓ₑ V
      → M ⇓ₑ W
        ---------------------
      → L `∨ᵉ M ⇓ₑ (V ⟦∨⟧ₑ W)

    ⇓ₑ-if-then : ∀ {L M N V ℓ}
      → L ⇓ₑ ($ᵉ true of ℓ)
      → M ⇓ₑ V
        ---------------------------------
      → ifᵉ L then M else N ⇓ₑ V

    ⇓ₑ-if-else : ∀ {L M N V ℓ}
      → L ⇓ₑ ($ᵉ false of ℓ)
      → N ⇓ₑ V
        ---------------------------------
      → ifᵉ L then M else N ⇓ₑ V

    ⇓ₑ-if-● : ∀ {L M N}
      → L ⇓ₑ ●
        ---------------------------------
      → ifᵉ L then M else N ⇓ₑ ●

    ⇓ₑ-app : ∀ {L M A} {N : ErasedTerm (∅ , A)} {V W ℓ}
      → L ⇓ₑ (ƛᵉ N of ℓ)
      → M ⇓ₑ V
      → N [ V ]ₑ ⇓ₑ W
        ---------------------------------
      → L ·ᵉ M ⇓ₑ stampₑ W ℓ

    ⇓ₑ-app-● : ∀ {L M V}
      → L ⇓ₑ ●
      → M ⇓ₑ V
        ---------------------------------
      → L ·ᵉ M ⇓ₑ ●

  mutual

    erase-renameᵛ : ∀ {Γ Δ T ℓ} (ρ : Γ →ʳ Δ) (V : Γ ⊢ᵛ T of ℓ) (ζ : ℒ)
        -------------------------------------------------------------------
      → eraseᵛ (renameᵛ ρ V) ζ (ℓ ⊑? ζ) ≡ renameₑ ρ (eraseᵛ V ζ (ℓ ⊑? ζ))
    erase-renameᵛ ρ ($ b of ℓ) ζ with ℓ ⊑? ζ
    ... | yes _ = refl
    ... | no _ = refl
    erase-renameᵛ {T = A ⇒ (B of ℓ′)} ρ (ƛ N of ℓ) ζ with ℓ ⊑? ζ
    ... | yes _ =
      cong (λ M → ƛᵉ M of ℓ)
           (trans (erase-renameᵉ (ext ρ) N ζ)
                  (renameₑ-cong (λ where
                    Z     → refl
                    (S x) → refl)
                    (erase N ζ (ℓ′ ⊑? ζ))))
    ... | no _ = refl

    erase-renameᵉ : ∀ {Γ Δ T ℓ} (ρ : Γ →ʳ Δ) (M : Γ ⊢ᵉ T of ℓ) (ζ : ℒ)
        -------------------------------------------------------------------
      → erase (renameᵉ ρ M) ζ (ℓ ⊑? ζ) ≡ renameₑ ρ (erase M ζ (ℓ ⊑? ζ))
    erase-renameᵉ ρ (` x) ζ = refl
    erase-renameᵉ ρ (val V) ζ = erase-renameᵛ ρ V ζ
    erase-renameᵉ ρ (L · M) ζ = cong₂ _·ᵉ_ (erase-renameᵉ ρ L ζ) (erase-renameᵉ ρ M ζ)
    erase-renameᵉ ρ (if L then M else N) ζ =
      cong₃ ifᵉ_then_else_ (erase-renameᵉ ρ L ζ) (erase-renameᵉ ρ M ζ) (erase-renameᵉ ρ N ζ)
    erase-renameᵉ ρ (M `∧ N) ζ = cong₂ _`∧ᵉ_ (erase-renameᵉ ρ M ζ) (erase-renameᵉ ρ N ζ)
    erase-renameᵉ ρ (M `∨ N) ζ = cong₂ _`∨ᵉ_ (erase-renameᵉ ρ M ζ) (erase-renameᵉ ρ N ζ)
    erase-renameᵉ {T = T₂} {ℓ = ℓ₂} ρ (sub {A = T₁ of ℓ₁} M A<:B) ζ with ℓ₂ ⊑? ζ
    ... | yes _ = erase-renameᵉ {T = T₁} {ℓ = ℓ₁} ρ M ζ
    ... | no _ = refl

  eraseˢ-exts : ∀ {Γ Δ A T ℓ} (σ : Γ →ˢ Δ) (ζ : ℒ) (x : Γ , A ∋ T of ℓ)
    → eraseˢ (exts σ) ζ x ≡ extsₑ (eraseˢ σ ζ) x
  eraseˢ-exts {A = A} σ ζ Z = refl
  eraseˢ-exts {A = A} {T = T} {ℓ = ℓ} σ ζ (S x) =
    erase-renameᵉ (S_ {B = A}) (σ x) ζ

  mutual

    erase-substᵛ : ∀ {Γ Δ T ℓ} (σ : Γ →ˢ Δ) (ζ : ℒ)
      → (V : Γ ⊢ᵛ T of ℓ)
        -------------------------------------------------------------------
      → eraseᵛ (substᵛ σ V) ζ (ℓ ⊑? ζ) ≡ substₑ (eraseˢ σ ζ) (eraseᵛ V ζ (ℓ ⊑? ζ))
    erase-substᵛ σ ζ ($ b of ℓ) with ℓ ⊑? ζ
    ... | yes _ = refl
    ... | no _ = refl
    erase-substᵛ {T = A ⇒ (B of ℓ′)} σ ζ (ƛ N of ℓ) with ℓ ⊑? ζ
    ... | yes _ =
      cong (λ M → ƛᵉ M of ℓ)
           (trans (erase-substᵉ (exts {A = A} σ) ζ N)
                  (substₑ-cong σ=τ (erase N ζ (ℓ′ ⊑? ζ))))
      where
      σ=τ : ∀ {A₁} (x : _ ∋ A₁)
        → eraseˢ (exts {A = A} σ) ζ x ≡ extsₑ {A = A} (eraseˢ σ ζ) x
      σ=τ {A₁ = T of ℓ₁} x = eraseˢ-exts {A = A} σ ζ x
    ... | no _ = refl

    erase-substᵉ : ∀ {Γ Δ T ℓ} (σ : Γ →ˢ Δ) (ζ : ℒ)
      → (M : Γ ⊢ᵉ T of ℓ)
        -------------------------------------------------------------------
      → erase (substᵉ σ M) ζ (ℓ ⊑? ζ) ≡ substₑ (eraseˢ σ ζ) (erase M ζ (ℓ ⊑? ζ))
    erase-substᵉ σ ζ (` x) = refl
    erase-substᵉ σ ζ (val V) = erase-substᵛ σ ζ V
    erase-substᵉ σ ζ (L · M) = cong₂ _·ᵉ_ (erase-substᵉ σ ζ L) (erase-substᵉ σ ζ M)
    erase-substᵉ σ ζ (if L then M else N) =
      cong₃ ifᵉ_then_else_ (erase-substᵉ σ ζ L)
                           (erase-substᵉ σ ζ M)
                           (erase-substᵉ σ ζ N)
    erase-substᵉ σ ζ (M `∧ N) = cong₂ _`∧ᵉ_ (erase-substᵉ σ ζ M) (erase-substᵉ σ ζ N)
    erase-substᵉ σ ζ (M `∨ N) = cong₂ _`∨ᵉ_ (erase-substᵉ σ ζ M) (erase-substᵉ σ ζ N)
    erase-substᵉ {T = T₂} {ℓ = ℓ₂} σ ζ (sub {A = T₁ of ℓ₁} M A<:B) with ℓ₂ ⊑? ζ
    ... | yes _ = erase-substᵉ {T = T₁} {ℓ = ℓ₁} σ ζ M
    ... | no _ = refl

  erase-[] : ∀ {A T ℓ₁ ℓ₂} {N : ∅ , A of ℓ₁ ⊢ᵉ T of ℓ₂} {V : ∅ ⊢ᵛ A of ℓ₁} {ζ}
      -----------------------------------------------------------------------------------------
    → erase (N [ val V ]) ζ (ℓ₂ ⊑? ζ) ≡ (erase N ζ (ℓ₂ ⊑? ζ) [ eraseᵛ V ζ (ℓ₁ ⊑? ζ) ]ₑ)
  erase-[] {A = A} {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {N = N} {V = V} {ζ = ζ} =
    trans (erase-substᵉ ((val V) • id) ζ N)
          (substₑ-cong erase-cons′ (erase N ζ (ℓ₂ ⊑? ζ)))
    where
    erase-cons′ : ∀ {B} (x : (∅ , (A of ℓ₁)) ∋ B) → eraseˢ ((val V) • id) ζ x ≡ (eraseᵛ V ζ (ℓ₁ ⊑? ζ) •ₑ idₑ) x
    erase-cons′ Z with ℓ₁ ⊑? ζ
    ... | yes _ = refl
    ... | no _ = refl
    erase-cons′ (S ())

  eraseᵛ-stamp-visible : ∀ {T ℓ₁ ζ} (V : ∅ ⊢ᵛ T of ℓ₁) (ℓ₂ : ℒ)
    → ℓ₂ ⊑ ζ
    → eraseᵛ (stamp-val V ℓ₂) ζ (ℓ₁ ⊔ ℓ₂ ⊑? ζ) ≡ stampₑ (eraseᵛ V ζ (ℓ₁ ⊑? ζ)) ℓ₂
  eraseᵛ-stamp-visible {ζ = ζ} ($ b of ℓ₁) ℓ₂ vis with (ℓ₁ ⊔ ℓ₂) ⊑? ζ | ℓ₁ ⊑? ζ
  ... | yes _ | yes _ = refl
  ... | yes res | no ¬ℓ₁⊑ζ = contradiction (⊑-trans ⊔-upper₁ res) ¬ℓ₁⊑ζ
  ... | no ¬res | yes ℓ₁⊑ζ = contradiction (⊔-least ℓ₁⊑ζ vis) ¬res
  ... | no _ | no _ = refl
  eraseᵛ-stamp-visible {T = A ⇒ (B of ℓ′)} {ζ = ζ} (ƛ N of ℓ₁) ℓ₂ vis with (ℓ₁ ⊔ ℓ₂) ⊑? ζ | ℓ₁ ⊑? ζ
  ... | yes _ | yes _ = refl
  ... | yes res | no ¬ℓ₁⊑ζ = contradiction (⊑-trans ⊔-upper₁ res) ¬ℓ₁⊑ζ
  ... | no ¬res | yes ℓ₁⊑ζ = contradiction (⊔-least ℓ₁⊑ζ vis) ¬res
  ... | no _ | no _ = refl

  eraseᵛ-⟦∧⟧ : ∀ {b₁ b₂ ℓ₁ ℓ₂ ζ}
    → (eraseᵛ ($ b₁ of ℓ₁) ζ (ℓ₁ ⊑? ζ) ⟦∧⟧ₑ eraseᵛ ($ b₂ of ℓ₂) ζ (ℓ₂ ⊑? ζ))
      ≡ eraseᵛ ($ (b₁ ∧ b₂) of (ℓ₁ ⊔ ℓ₂)) ζ ((ℓ₁ ⊔ ℓ₂) ⊑? ζ)
  eraseᵛ-⟦∧⟧ {b₁} {b₂} {ℓ₁} {ℓ₂} {ζ} with ℓ₁ ⊑? ζ | ℓ₂ ⊑? ζ | (ℓ₁ ⊔ ℓ₂) ⊑? ζ
  ... | yes _ | yes _ | yes _ = refl
  ... | yes ℓ₁⊑ζ | yes ℓ₂⊑ζ | no ¬vis = contradiction (⊔-least ℓ₁⊑ζ ℓ₂⊑ζ) ¬vis
  ... | yes _ | no ¬ℓ₂⊑ζ | yes vis = contradiction (⊑-trans ⊔-upper₂ vis) ¬ℓ₂⊑ζ
  ... | no ¬ℓ₁⊑ζ | yes _ | yes vis = contradiction (⊑-trans ⊔-upper₁ vis) ¬ℓ₁⊑ζ
  ... | no ¬ℓ₁⊑ζ | no _ | yes vis = contradiction (⊑-trans ⊔-upper₁ vis) ¬ℓ₁⊑ζ
  ... | yes _ | no _ | no _ = refl
  ... | no _ | yes _ | no _ = refl
  ... | no _ | no _ | no _ = refl

  eraseᵛ-⟦∨⟧ : ∀ {b₁ b₂ ℓ₁ ℓ₂ ζ}
    → (eraseᵛ ($ b₁ of ℓ₁) ζ (ℓ₁ ⊑? ζ) ⟦∨⟧ₑ eraseᵛ ($ b₂ of ℓ₂) ζ (ℓ₂ ⊑? ζ))
      ≡ eraseᵛ ($ (b₁ ∨ b₂) of (ℓ₁ ⊔ ℓ₂)) ζ ((ℓ₁ ⊔ ℓ₂) ⊑? ζ)
  eraseᵛ-⟦∨⟧ {b₁} {b₂} {ℓ₁} {ℓ₂} {ζ} with ℓ₁ ⊑? ζ | ℓ₂ ⊑? ζ | (ℓ₁ ⊔ ℓ₂) ⊑? ζ
  ... | yes _ | yes _ | yes _ = refl
  ... | yes ℓ₁⊑ζ | yes ℓ₂⊑ζ | no ¬vis = contradiction (⊔-least ℓ₁⊑ζ ℓ₂⊑ζ) ¬vis
  ... | yes _ | no ¬ℓ₂⊑ζ | yes vis = contradiction (⊑-trans ⊔-upper₂ vis) ¬ℓ₂⊑ζ
  ... | no ¬ℓ₁⊑ζ | yes _ | yes vis = contradiction (⊑-trans ⊔-upper₁ vis) ¬ℓ₁⊑ζ
  ... | no ¬ℓ₁⊑ζ | no _ | yes vis = contradiction (⊑-trans ⊔-upper₁ vis) ¬ℓ₁⊑ζ
  ... | yes _ | no _ | no _ = refl
  ... | no _ | yes _ | no _ = refl
  ... | no _ | no _ | no _ = refl

  eraseᵛ-value : ∀ {T ℓ} (V : ∅ ⊢ᵛ T of ℓ) (ζ : ℒ)
    → ErasedValue (eraseᵛ V ζ (ℓ ⊑? ζ))
  eraseᵛ-value ($ b of ℓ) ζ with ℓ ⊑? ζ
  ... | yes _ = V-$ᵉ
  ... | no _ = V-●
  eraseᵛ-value {T = A ⇒ (B of ℓ′)} (ƛ N of ℓ) ζ with ℓ ⊑? ζ
  ... | yes _ = V-ƛᵉ
  ... | no _ = V-●

  eraseᵛ-no : ∀ {Γ T ℓ ζ} (V : Γ ⊢ᵛ T of ℓ) (¬ℓ⊑ζ : ¬ (ℓ ⊑ ζ))
      → eraseᵛ V ζ (no ¬ℓ⊑ζ) ≡ ●
  eraseᵛ-no {T = `𝔹} ($ b of ℓ) ¬ℓ⊑ζ = refl
  eraseᵛ-no {T = A ⇒ (B of ℓ′)} (ƛ N of ℓ) ¬ℓ⊑ζ = refl

  eraseᵛ-hidden : ∀ {Γ T ℓ ζ} (V : Γ ⊢ᵛ T of ℓ) (¬ℓ⊑ζ : ¬ (ℓ ⊑ ζ))
      → eraseᵛ V ζ (ℓ ⊑? ζ) ≡ ●
  eraseᵛ-hidden {ℓ = ℓ} {ζ = ζ} V ¬ℓ⊑ζ with ℓ ⊑? ζ
  ... | yes ℓ⊑ζ = contradiction ℓ⊑ζ ¬ℓ⊑ζ
  ... | no ¬a = eraseᵛ-no V ¬a

  mutual

    sim-bool-visible : ∀ {b ℓ ζ} {M : ∅ ⊢ᵉ `𝔹 of ℓ}
        → M ⇓ ($ b of ℓ)
        → (ℓ⊑ζ : ℓ ⊑ ζ)
          ---------------------------------------------
        → erase M ζ (ℓ ⊑? ζ) ⇓ₑ $ᵉ b of ℓ
    sim-bool-visible {b} {ℓ} {ζ} {M = M} M⇓V ℓ⊑ζ with ℓ ⊑? ζ in eq
    ... | yes _ =
      subst (λ d → erase M ζ d ⇓ₑ eraseᵛ ($ b of ℓ) ζ d) eq (sim M⇓V)
    ... | no ¬ℓ⊑ζ = contradiction ℓ⊑ζ ¬ℓ⊑ζ

    sim-lam-visible : ∀ {A B ℓ ℓ′ ζ} {M : ∅ ⊢ᵉ (A ⇒ B of ℓ′) of ℓ} {N}
      → M ⇓ ƛ N of ℓ
      → ℓ ⊑ ζ
        ---------------------------------------------------------
      → erase M ζ (ℓ ⊑? ζ) ⇓ₑ ƛᵉ (erase N ζ (ℓ′ ⊑? ζ)) of ℓ
    sim-lam-visible {A} {B} {ℓ} {ℓ′} {ζ} {M = M} {N = N} M⇓V ℓ⊑ζ with ℓ ⊑? ζ in eq
    ... | yes _ =
      subst (λ d → erase M ζ d ⇓ₑ eraseᵛ (ƛ N of ℓ) ζ d) eq (sim M⇓V)
    ... | no ¬ℓ⊑ζ = contradiction ℓ⊑ζ ¬ℓ⊑ζ

    sim : ∀ {T ℓ ζ} {M : ∅ ⊢ᵉ T of ℓ} {V : ∅ ⊢ᵛ T of ℓ}
      → M ⇓ V
      ----------------------------------------------------------------------------------
      → erase M ζ (ℓ ⊑? ζ) ⇓ₑ eraseᵛ V ζ (ℓ ⊑? ζ)
    sim {ζ = ζ} (⇓-val {V = V}) = ⇓ₑ-val (eraseᵛ-value V ζ)

    sim {ζ = ζ} {M = M `∧ N} (⇓-∧ {V = $ b₁ of ℓ₁} {W = $ b₂ of ℓ₂} M⇓V N⇓W) =
      subst (λ □ → erase (M `∧ N) ζ ((ℓ₁ ⊔ ℓ₂) ⊑? ζ) ⇓ₑ □)
            (eraseᵛ-⟦∧⟧ {b₁} {b₂} {ℓ₁} {ℓ₂} {ζ})
            (⇓ₑ-∧ (sim M⇓V) (sim N⇓W))

    sim {ζ = ζ} {M = M `∨ N} (⇓-∨ {V = $ b₁ of ℓ₁} {W = $ b₂ of ℓ₂} M⇓V N⇓W) =
      subst (λ □ → erase (M `∨ N) ζ ((ℓ₁ ⊔ ℓ₂) ⊑? ζ) ⇓ₑ □)
            (eraseᵛ-⟦∨⟧ {b₁} {b₂} {ℓ₁} {ℓ₂} {ζ})
            (⇓ₑ-∨ (sim M⇓V) (sim N⇓W))

    sim {ζ = ζ} {M = if L then M₁ else N₁} (⇓-if-then {ℓₗ = ℓₗ} {ℓ₂ = ℓ₂} {V = V} {L = L} {M = M₁} {N = N₁} L⇓true M⇓V)
      with ℓₗ ⊑? ζ in eq
    ... | yes vis = ⇓ₑ-if-then
                       (subst (λ d → erase L ζ d ⇓ₑ $ᵉ true of ℓₗ) eq
                              (sim-bool-visible L⇓true vis))
                       (sim M⇓V)
    ... | no ¬vis =
      subst
        (λ □ → ifᵉ erase L ζ (no ¬vis) then erase M₁ ζ ((ℓ₂ ⊔ ℓₗ) ⊑? ζ) else erase N₁ ζ ((ℓ₂ ⊔ ℓₗ) ⊑? ζ)
             ⇓ₑ □)
        (sym (eraseᵛ-hidden V (λ vis → ¬vis (⊑-trans ⊔-upper₂ vis))))
        (⇓ₑ-if-●
          (subst
            (λ □ → erase L ζ (no ¬vis) ⇓ₑ □)
            (eraseᵛ-hidden ($ true of ℓₗ) ¬vis)
            (subst (λ d → erase L ζ d ⇓ₑ eraseᵛ ($ true of ℓₗ) ζ (ℓₗ ⊑? ζ)) eq
                   (sim L⇓true))))

    sim {ζ = ζ} {M = if L then M₁ else N₁} (⇓-if-else {ℓₗ = ℓₗ} {ℓ₂ = ℓ₂} {V = V} {L = L} {M = M₁} {N = N₁} L⇓false N⇓V)
      with ℓₗ ⊑? ζ in eq
    ... | yes vis = ⇓ₑ-if-else
                       (subst (λ d → erase L ζ d ⇓ₑ $ᵉ false of ℓₗ) eq
                              (sim-bool-visible L⇓false vis))
                       (sim N⇓V)
    ... | no ¬vis =
      subst
        (λ □ → ifᵉ erase L ζ (no ¬vis) then erase M₁ ζ ((ℓ₂ ⊔ ℓₗ) ⊑? ζ) else erase N₁ ζ ((ℓ₂ ⊔ ℓₗ) ⊑? ζ)
             ⇓ₑ □)
        (sym (eraseᵛ-hidden V (λ vis → ¬vis (⊑-trans ⊔-upper₂ vis))))
        (⇓ₑ-if-●
          (subst
            (λ □ → erase L ζ (no ¬vis) ⇓ₑ □)
            (eraseᵛ-hidden ($ false of ℓₗ) ¬vis)
            (subst (λ d → erase L ζ d ⇓ₑ eraseᵛ ($ false of ℓₗ) ζ (ℓₗ ⊑? ζ)) eq
                   (sim L⇓false))))

    sim {ζ = ζ} {M = L · M₁} (⇓-app {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₃} {W = W} {V = V} {N = N} {L = L} {M = M₁} L⇓ƛ M⇓W N[W]⇓V)
      with ℓ₃ ⊑? ζ in eq
    ... | yes vis =
      subst
        (λ □ → erase L ζ (yes vis) ·ᵉ erase M₁ ζ (_ ⊑? ζ) ⇓ₑ □)
        (sym (eraseᵛ-stamp-visible V ℓ₃ vis))
        (⇓ₑ-app (subst (λ d → erase L ζ d ⇓ₑ ƛᵉ (erase N ζ (_ ⊑? ζ)) of ℓ₃) eq
                         (sim-lam-visible L⇓ƛ vis))
                 (sim M⇓W)
                 (subst
                   (λ □ → □ ⇓ₑ eraseᵛ V ζ (_ ⊑? ζ))
                   (erase-[] {N = N} {V = W} {ζ = ζ})
                   (sim N[W]⇓V)))
    ... | no ¬vis =
      subst
        (λ □ → erase L ζ (no ¬vis) ·ᵉ erase M₁ ζ (_ ⊑? ζ) ⇓ₑ □)
        (sym (eraseᵛ-hidden (stamp-val V ℓ₃) (λ vis → ¬vis (⊑-trans ⊔-upper₂ vis))))
        (⇓ₑ-app-●
          (subst
            (λ □ → erase L ζ (no ¬vis) ⇓ₑ □)
            (eraseᵛ-hidden (ƛ N of ℓ₃) ¬vis)
            (subst (λ d → erase L ζ d ⇓ₑ eraseᵛ (ƛ N of ℓ₃) ζ (ℓ₃ ⊑? ζ)) eq
                   (sim L⇓ƛ)))
          (sim M⇓W))
