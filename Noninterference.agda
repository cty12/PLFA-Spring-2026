open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)


record LabelLattice : Set₁ where

  infix 4  _⊑_
  infixl 6 _⊔_
  infix 4  _⊑?_

  field
    ℒ        : Set
    ⊥ₗ       : ℒ
    _⊔_      : ℒ → ℒ → ℒ
    _⊑_      : ℒ → ℒ → Set
    _≟ₗ_     : ∀ (ℓ₁ ℓ₂ : ℒ) → Dec (ℓ₁ ≡ ℓ₂)
    _⊑?_     : ∀ (ℓ₁ ℓ₂ : ℒ) → Dec (ℓ₁ ⊑ ℓ₂)

    ⊑-refl   : ∀ {ℓ} → ℓ ⊑ ℓ
    ⊑-trans  : ∀ {ℓ₁ ℓ₂ ℓ₃} → ℓ₁ ⊑ ℓ₂ → ℓ₂ ⊑ ℓ₃ → ℓ₁ ⊑ ℓ₃
    ⊑-antisym : ∀ {ℓ₁ ℓ₂} → ℓ₁ ⊑ ℓ₂ → ℓ₂ ⊑ ℓ₁ → ℓ₁ ≡ ℓ₂

    ⊥ₗ-least : ∀ {ℓ} → ⊥ₗ ⊑ ℓ
    ⊔-upper₁ : ∀ {ℓ₁ ℓ₂} → ℓ₁ ⊑ (ℓ₁ ⊔ ℓ₂)
    ⊔-upper₂ : ∀ {ℓ₁ ℓ₂} → ℓ₂ ⊑ (ℓ₁ ⊔ ℓ₂)
    ⊔-least  : ∀ {ℓ₁ ℓ₂ ℓ} → ℓ₁ ⊑ ℓ → ℓ₂ ⊑ ℓ → (ℓ₁ ⊔ ℓ₂) ⊑ ℓ


module IFC (𝑳 : LabelLattice) where

  open LabelLattice 𝑳 public

  infix  4 _⊢ᵛ_
  infix  4 _⊢ᵉ_
  infix  4 _∋_
  infixl 5 _,_

  infixr 6 _⇒_
  infix  7 _of_

  infix  5 ƛ_of_
  infix 6 if_then_else_
  infixl 7 _·_
  infixl 8 _`∧_
  infixl 8 _`∨_
  infix  9 val_
  infix  9 $_of_
  infix  9 `_
  infix  9 S_


  data Type : Set; data SecType : Set

  data Type where
    `𝔹   : Type
    _⇒_ : SecType → SecType → Type

  data SecType where
    _of_ : Type → ℒ → SecType

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


  -- label stamping on types
  stamp : SecType → ℒ → SecType
  stamp (T of ℓ₁) ℓ₂ = T of (ℓ₁ ⊔ ℓ₂)

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


  data _⊢ᵛ_ : Context → SecType → Set
  data _⊢ᵉ_ : Context → SecType → Set

  -- values
  data _⊢ᵛ_ where

    $_of_ : ∀ {Γ}
      → (b : Bool)
      → (ℓ : ℒ)
        ------------------- (Tv-Bool)
      → Γ ⊢ᵛ `𝔹 of ℓ

    -- FUN:
    ƛ_of_  : ∀ {Γ A B}
      → (Γ , A) ⊢ᵉ B
      → (ℓ : ℒ)
        ------------------------ (Tv-Abs)
      → Γ ⊢ᵛ (A ⇒ B) of ℓ

  stamp-val : ∀ {Γ A} → Γ ⊢ᵛ A → (ℓ : ℒ) → Γ ⊢ᵛ (stamp A ℓ)
  stamp-val ($ b of ℓ₁) ℓ₂ = $ b of (ℓ₁ ⊔ ℓ₂)
  stamp-val (ƛ N of ℓ₁) ℓ₂ = ƛ N of (ℓ₁ ⊔ ℓ₂)

  -- intrinsically-typed terms inhibit a typing judgement
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

  _→ʳ_ _→ˢ_ : Context → Context → Set
  Γ →ʳ Δ = ∀ {X} → Γ ∋ X → Δ ∋ X
  Γ →ˢ Δ = ∀ {X} → Γ ∋ X → Δ ⊢ᵉ X

  ext : ∀ {Γ Δ A} → Γ →ʳ Δ → (Γ , A) →ʳ (Δ , A)
  ext ρ Z      =  Z
  ext ρ (S x)  =  S (ρ x)

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

  exts : ∀ {Γ Δ A} → Γ →ˢ Δ → (Γ , A) →ˢ (Δ , A)
  exts σ Z      =  ` Z
  exts σ (S x)  =  renameᵉ S_ (σ x)

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

  _•_ : ∀ {Γ Δ A} → Δ ⊢ᵉ A → Γ →ˢ Δ → (Γ , A) →ˢ Δ
  (M • σ) Z = M
  (M • σ) (S x) = σ x

  σ₀ : ∀ {Γ A} → Γ ⊢ᵉ A → (Γ , A) →ˢ Γ
  σ₀ M Z      =  M
  σ₀ M (S x)  =  ` x

  _[_] : ∀ {Γ A B} → Γ , A ⊢ᵉ B → Γ ⊢ᵉ A → Γ ⊢ᵉ B
  N [ M ] =  substᵉ (σ₀ M) N

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
