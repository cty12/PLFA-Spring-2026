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

  subst-congᵛ : ∀ {Γ Δ A} {σ τ : Γ →ˢ Δ}
      → (∀ {B} (x : Γ ∋ B) → σ x ≡ τ x)
      → (V : Γ ⊢ᵛ A)
      → substᵛ σ V ≡ substᵛ τ V
  subst-congᵉ : ∀ {Γ Δ A} {σ τ : Γ →ˢ Δ}
      → (∀ {B} (x : Γ ∋ B) → σ x ≡ τ x)
      → (M : Γ ⊢ᵉ A)
      → substᵉ σ M ≡ substᵉ τ M
  subst-congᵛ {σ = σ} {τ} σ=τ (ƛ N of ℓ) =
    cong (λ N′ → ƛ N′ of ℓ) (subst-congᵉ exts[σ]=exts[τ] N)
    where
    exts[σ]=exts[τ] : ∀ {A} (x : _ ∋ A) → exts σ x ≡ exts τ x
    exts[σ]=exts[τ] Z     = refl
    exts[σ]=exts[τ] (S x) = cong (renameᵉ S_) (σ=τ x)
  subst-congᵛ σ=τ ($ b of ℓ) = refl
  subst-congᵉ σ=τ (` x) = σ=τ x
  subst-congᵉ σ=τ (val V) = cong val_ (subst-congᵛ σ=τ V)
  subst-congᵉ σ=τ (L · M) = cong₂ _·_ (subst-congᵉ σ=τ L) (subst-congᵉ σ=τ M)
  subst-congᵉ σ=τ (if L then M else N) =
    cong₃ if_then_else_ (subst-congᵉ σ=τ L) (subst-congᵉ σ=τ M) (subst-congᵉ σ=τ N)
  subst-congᵉ σ=τ (M `∧ N) = cong₂ _`∧_ (subst-congᵉ σ=τ M) (subst-congᵉ σ=τ N)
  subst-congᵉ σ=τ (M `∨ N) = cong₂ _`∨_ (subst-congᵉ σ=τ M) (subst-congᵉ σ=τ N)
  subst-congᵉ σ=τ (sub M A<:B) = cong (λ M′ → sub M′ A<:B) (subst-congᵉ σ=τ M)

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

  -- | Logical relations
  infix 0 _of_⦂_≈ᵛ⦅_⦆_ _of_⦂_≈ᵉ⦅_⦆_ _⊢_≈⦅_⦆_

  _of_⦂_≈ᵛ⦅_⦆_ : ∀ T ℓ → ∅ ⊢ᵛ T of ℓ → ℒ → ∅ ⊢ᵛ T of ℓ → Set
  _of_⦂_≈ᵉ⦅_⦆_ : ∀ T ℓ → ∅ ⊢ᵉ T of ℓ → ℒ → ∅ ⊢ᵉ T of ℓ → Set

  `𝔹                     of ℓ ⦂ V ≈ᵛ⦅ ζ ⦆ W = ℓ ⊑ ζ → V ≡ W
  (T₁ of ℓ₁ ⇒ T₂ of ℓ₂) of ℓ ⦂ V ≈ᵛ⦅ ζ ⦆ W =
    ℓ ⊑ ζ → ∀ {V′ W′}
          → T₁ of ℓ₁       ⦂ V′ ≈ᵛ⦅ ζ ⦆ W′
          → T₂ of (ℓ₂ ⊔ ℓ) ⦂ (val V) · (val V′) ≈ᵉ⦅ ζ ⦆ (val W) · (val W′)

  T of ℓ ⦂ M ≈ᵉ⦅ ζ ⦆ N = ∀ {V W} → M ⇓ V → N ⇓ W → T of ℓ ⦂ V ≈ᵛ⦅ ζ ⦆ W

  ≈ᵛ→≈ᵉ : ∀ {T ℓ ζ V W} → T of ℓ ⦂ V ≈ᵛ⦅ ζ ⦆ W → T of ℓ ⦂ val V ≈ᵉ⦅ ζ ⦆ val W
  ≈ᵛ→≈ᵉ V≈W ⇓-val ⇓-val = V≈W

  _⊢_≈⦅_⦆_ : ∀ Γ → Γ →ˢ ∅ → ℒ → Γ →ˢ ∅ → Set
  Γ ⊢ σ₁ ≈⦅ ζ ⦆ σ₂ = ∀ {T ℓ} x → T of ℓ ⦂ σ₁ x ≈ᵉ⦅ ζ ⦆ σ₂ x

  record RelSub (Γ : Context) (ζ : ℒ) : Set where
    constructor relSub
    field
      σ₁ : Γ →ˢ ∅
      σ₂ : Γ →ˢ ∅
      σ≈ : Γ ⊢ σ₁ ≈⦅ ζ ⦆ σ₂

  open RelSub public

  extendRelSub : ∀ {Γ T ℓ ζ} {M N : ∅ ⊢ᵉ T of ℓ}
    → RelSub Γ ζ
    → T of ℓ ⦂ M ≈ᵉ⦅ ζ ⦆ N
      ---------------------------------------------
    → RelSub (Γ , T of ℓ) ζ
  extendRelSub {Γ = Γ} {T} {ℓ} {ζ} {M} {N} γ M≈N =
    relSub (M • γ .σ₁) (N • γ .σ₂) σ≈-•
    where
    σ≈-• : (Γ , T of ℓ) ⊢ (M • γ .σ₁) ≈⦅ ζ ⦆ (N • γ .σ₂)
    σ≈-• Z     = M≈N
    σ≈-• (S x) = σ≈ γ x

  stamp-val-assoc : ∀ {Γ T ℓ} (V : Γ ⊢ᵛ T of ℓ) {ℓ₁ ℓ₂}
      →                                    stamp-val (stamp-val V ℓ₁) ℓ₂   ≡
         subst (λ □ → Γ ⊢ᵛ T of □) (sym ⊔-assoc) (stamp-val V (ℓ₁ ⊔ ℓ₂))
  stamp-val-assoc ($ b of ℓ) {ℓ₁} {ℓ₂} rewrite ⊔-assoc {ℓ} {ℓ₁} {ℓ₂} = refl
  stamp-val-assoc (ƛ N of ℓ) {ℓ₁} {ℓ₂} rewrite ⊔-assoc {ℓ} {ℓ₁} {ℓ₂} = refl
  {-# REWRITE stamp-val-assoc #-}

  private
    cong≈ : ∀ {T ℓ₁ ℓ₂ ζ} {V W : ∅ ⊢ᵛ T of ℓ₁} {V′ W′ : ∅ ⊢ᵛ T of ℓ₂}
      → (ℓ₁=ℓ₂ : ℓ₁ ≡ ℓ₂)
      → V ≡ subst (λ □ → ∅ ⊢ᵛ T of □) (sym ℓ₁=ℓ₂) V′
      → W ≡ subst (λ □ → ∅ ⊢ᵛ T of □) (sym ℓ₁=ℓ₂) W′
        ------------------------------------------------------
      → (T of ℓ₁ ⦂ V ≈ᵛ⦅ ζ ⦆ W) ≡ (T of ℓ₂ ⦂ V′ ≈ᵛ⦅ ζ ⦆ W′)
    cong≈ refl refl refl = refl

    stamp-pres-≈ : ∀ {T ℓ ζ} {V W : ∅ ⊢ᵛ T of ℓ}
      → (ℓ′ : ℒ)
      → T of ℓ ⦂ V ≈ᵛ⦅ ζ ⦆ W
        ------------------------------------------------------------
      → T of (ℓ ⊔ ℓ′) ⦂ stamp-val V ℓ′ ≈ᵛ⦅ ζ ⦆ stamp-val W ℓ′
    stamp-pres-≈ {T = `𝔹} {ℓ} {V = V} {W = W} ℓ′ V≈W ℓ⊔ℓ′⊑ζ =
      cong (λ □ → stamp-val □ ℓ′) (V≈W (⊑-trans ⊔-upper₁ ℓ⊔ℓ′⊑ζ))
    stamp-pres-≈ {T = T₁ of ℓ₁ ⇒ T₂ of ℓ₂} {V = ƛ N₁ of ℓ₃} {ƛ N₂ of .ℓ₃} ℓ₄ V≈W ℓ⊔ℓ′⊑ζ V′≈W′
      (⇓-app ⇓-val ⇓-val N₁[V′]⇓V₁)
      (⇓-app ⇓-val ⇓-val N₂[W′]⇓W₁) =
        subst (λ □ → □) (cong≈ ⊔-assoc refl refl)
          (stamp-pres-≈ ℓ₄ (V≈W (⊑-trans ⊔-upper₁ ℓ⊔ℓ′⊑ζ) V′≈W′
                                (⇓-app ⇓-val ⇓-val N₁[V′]⇓V₁)
                                (⇓-app ⇓-val ⇓-val N₂[W′]⇓W₁)))

  fundamental : ∀ {Γ T ℓ ζ}
    → (M : Γ ⊢ᵉ T of ℓ)
    → (γ : RelSub Γ ζ)
      ------------------------------------------------------------
    → T of ℓ ⦂ (substᵉ (γ .σ₁) M) ≈ᵉ⦅ ζ ⦆ (substᵉ (γ .σ₂) M)
  fundamental (` x) γ = (γ .σ≈) x
  fundamental (val ($ b of ℓ)) γ ⇓-val ⇓-val _ = refl
  fundamental {T = (T₁ of ℓ₁) ⇒ (T₂ of ℓ₂)}
    (val (ƛ N of ℓ)) γ ⇓-val ⇓-val ℓ⊑ζ {V′} {W′} V′≈W′
    (⇓-app {V = V₁} ⇓-val ⇓-val N[V′]⇓V₁)
    (⇓-app {V = W₁} ⇓-val ⇓-val N[W′]⇓W₁) =
      stamp-pres-≈ ℓ (fundamental N (extendRelSub γ (≈ᵛ→≈ᵉ V′≈W′)) N[V′]⇓V₁ N[W′]⇓W₁)
  fundamental (_`∧_ M N) γ
    (⇓-∧ M⇓V₁ N⇓W₁) (⇓-∧ M⇓V₂ N⇓W₂) ℓ₁⊔ℓ₂⊑ζ =
      cong₂ _⟦∧⟧_ (fundamental M γ M⇓V₁ M⇓V₂ (⊑-trans ⊔-upper₁ ℓ₁⊔ℓ₂⊑ζ))
                  (fundamental N γ N⇓W₁ N⇓W₂ (⊑-trans ⊔-upper₂ ℓ₁⊔ℓ₂⊑ζ))
  fundamental (_`∨_ {ℓ₁ = ℓ₁} {ℓ₂} M N) γ
    (⇓-∨ M⇓V₁ N⇓W₁) (⇓-∨ M⇓V₂ N⇓W₂) ℓ₁⊔ℓ₂⊑ζ =
      cong₂ _⟦∨⟧_ (fundamental M γ M⇓V₁ M⇓V₂ (⊑-trans ⊔-upper₁ ℓ₁⊔ℓ₂⊑ζ))
                  (fundamental N γ N⇓W₁ N⇓W₂ (⊑-trans ⊔-upper₂ ℓ₁⊔ℓ₂⊑ζ))
  fundamental {ζ = ζ} (_·_ {T = T} {ℓ₃ = ℓ₃} L M) γ
    (⇓-app L⇓₁ M⇓₁ N[V]⇓V₁) (⇓-app L⇓₂ M⇓₂ N[W]⇓W₁)
    with ℓ₃ ⊑? ζ
  ... | yes ℓ₃⊑ζ =
    fundamental L γ L⇓₁ L⇓₂ ℓ₃⊑ζ
      (fundamental M γ M⇓₁ M⇓₂)
      (⇓-app ⇓-val ⇓-val N[V]⇓V₁) (⇓-app ⇓-val ⇓-val N[W]⇓W₁)
  ... | no ¬ℓ₃⊑ζ with T  -- we can see nothing regardless of the type
  ...   | `𝔹               = λ ℓ₂⊔ℓ₃⊑ζ → contradiction (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₃⊑ζ) ¬ℓ₃⊑ζ
  ...   | _ of _ ⇒ _ of _ = λ ℓ₂⊔ℓ₃⊑ζ → contradiction (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₃⊑ζ) ¬ℓ₃⊑ζ
  fundamental (if_then_else_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L M N) γ
    (⇓-if-then L⇓true M⇓V₁) (⇓-if-then L⇓true′ M⇓V₂) =
      fundamental M γ M⇓V₁ M⇓V₂
  fundamental (if_then_else_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L M N) γ
    (⇓-if-else L⇓false N⇓W₁) (⇓-if-else L⇓false′ N⇓W₂) =
      fundamental N γ N⇓W₁ N⇓W₂
  -- impossible cases
  fundamental (if_then_else_ {T = T} L M N) γ
    (⇓-if-then L⇓true M⇓V₁) (⇓-if-else L⇓false N⇓W₂) with T
  ... | `𝔹 =
    λ ℓ₂⊔ℓ₁⊑ζ →
      case fundamental L γ L⇓true L⇓false (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₁⊑ζ) of λ ()
  ... | _ of _ ⇒ _ of _ =
    λ ℓ₂⊔ℓ₁⊑ζ →
      case fundamental L γ L⇓true L⇓false (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₁⊑ζ) of λ ()
  fundamental (if_then_else_ {T = T} L M N) γ
    (⇓-if-else L⇓false N⇓W₁) (⇓-if-then L⇓true M⇓V₂) with T
  ... | `𝔹 =
    λ ℓ₂⊔ℓ₁⊑ζ →
      case fundamental L γ L⇓false L⇓true (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₁⊑ζ) of λ ()
  ... | _ of _ ⇒ _ of _ =
    λ ℓ₂⊔ℓ₁⊑ζ →
      case fundamental L γ L⇓false L⇓true (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₁⊑ζ) of λ ()

module TwoPointLattice where

  data SecLabel : Set where
    low high : SecLabel

  _⊔_ : SecLabel → SecLabel → SecLabel
  low  ⊔ ℓ    = ℓ
  high ⊔ _    = high

  _≟_ : ∀ (ℓ₁ ℓ₂ : SecLabel) → Dec (ℓ₁ ≡ ℓ₂)
  low  ≟ low  = yes refl
  high ≟ high = yes refl
  low  ≟ high = no λ ()
  high ≟ low  = no λ ()

  twoPointLattice : LabelLattice
  twoPointLattice = record
    { ℒ           = SecLabel
    ; ⊥ₗ          = low
    ; _⊔_         = _⊔_
    ; _≟ₗ_        = _≟_
    ; ⊥ₗ-identity = λ where
        {low}  → refl
        {high} → refl
    ; ⊔-assoc     = λ where
        {low}  {low}  {low}  → refl
        {low}  {low}  {high} → refl
        {low}  {high} {low}  → refl
        {low}  {high} {high} → refl
        {high} {low}  {low}  → refl
        {high} {low}  {high} → refl
        {high} {high} {low}  → refl
        {high} {high} {high} → refl
    ; ⊔-comm      = λ where
        {low}  {low}  → refl
        {low}  {high} → refl
        {high} {low}  → refl
        {high} {high} → refl
    ; ⊔-idem      = λ where
        {low}  → refl
        {high} → refl
    }

open TwoPointLattice using (twoPointLattice; high; low)
open λSec twoPointLattice public

noninterference : ∀ {T} {M : ∅ , T of high ⊢ᵉ `𝔹 of low}
                    {V₁ V₂ : ∅ ⊢ᵛ T of high} {V₁′ V₂′ : ∅ ⊢ᵛ `𝔹 of low}
  → M [ val V₁ ] ⇓ V₁′
  → M [ val V₂ ] ⇓ V₂′
    ---------------------------------
  → V₁′ ≡ V₂′
noninterference {T} {M} {V₁} {V₂} M[V₁]⇓V₁′ M[V₂]⇓V₂′ =
  fundamental M (relSub ((val V₁) • id) ((val V₂) • id) σ₀-rel)
              M[V₁]⇓V₁′ M[V₂]⇓V₂′ ⊑-refl
  where
  high-rel : ∀ T′ {V W} → T′ of high ⦂ V ≈ᵛ⦅ low ⦆ W
  high-rel `𝔹                 = λ ()
  high-rel (_ of _ ⇒ _ of _) = λ ()
  σ₀-rel : ∅ , T of high ⊢ (val V₁) • id ≈⦅ low ⦆ (val V₂) • id
  σ₀-rel Z = ≈ᵛ→≈ᵉ (high-rel T)
  σ₀-rel (S ())
