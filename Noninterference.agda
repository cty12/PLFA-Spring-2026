{-# OPTIONS --rewriting #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)

-- Need the following two imports for rewriting
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite


-- | The security lattice is a join semilattice with a bottom element (⊥ₗ)
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

  -- | Substitution
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


  postulate
    exts-sub-cons : ∀ {Γ Δ A B} (σ : Γ →ˢ Δ) (N : Γ , B ⊢ᵉ A) (M : Δ ⊢ᵉ B)
        ------------------------------------------------------------------------
      → (substᵉ (exts σ) N) [ M ] ≡ substᵉ (M • σ) N


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
  infix 0 _of_⦂_≈ᵛ⦅_⦆_ _of_⦂_≈ᵉ⦅_⦆_

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

  ≈-• : ∀ {Γ T ℓ ζ} {σ₁ σ₂ : Γ →ˢ ∅} {M N : ∅ ⊢ᵉ T of ℓ}
    → Γ ⊢ σ₁ ≈⦅ ζ ⦆ σ₂
    → T of ℓ ⦂ M ≈ᵉ⦅ ζ ⦆ N
    → (Γ , T of ℓ) ⊢ (M • σ₁) ≈⦅ ζ ⦆ (N • σ₂)
  ≈-• σ₁≈σ₂ M≈N Z = M≈N
  ≈-• σ₁≈σ₂ M≈N (S x) = σ₁≈σ₂ x

  ⊔-assoc : ∀ {ℓ₁ ℓ₂ ℓ₃}
    → (ℓ₁ ⊔ ℓ₂) ⊔ ℓ₃ ≡ ℓ₁ ⊔ (ℓ₂ ⊔ ℓ₃)
  ⊔-assoc {ℓ₁} {ℓ₂} {ℓ₃} =
    ⊑-antisym
      (⊔-least
        (⊔-least
          ⊔-upper₁
          (⊑-trans ⊔-upper₁ ⊔-upper₂))
        (⊑-trans ⊔-upper₂ ⊔-upper₂))
      (⊔-least
        (⊑-trans ⊔-upper₁ ⊔-upper₁)
        (⊔-least
          (⊑-trans ⊔-upper₂ ⊔-upper₁)
          ⊔-upper₂))

  stamp-val-assoc : ∀ {Γ T ℓ} (V : Γ ⊢ᵛ T of ℓ) {ℓ₁ ℓ₂}
      →                                    stamp-val (stamp-val V ℓ₁) ℓ₂   ≡
         subst (λ □ → Γ ⊢ᵛ T of □) (sym ⊔-assoc) (stamp-val V (ℓ₁ ⊔ ℓ₂))
  stamp-val-assoc ($ b of ℓ) {ℓ₁} {ℓ₂} rewrite ⊔-assoc {ℓ} {ℓ₁} {ℓ₂} = refl
  stamp-val-assoc (ƛ N of ℓ) {ℓ₁} {ℓ₂} rewrite ⊔-assoc {ℓ} {ℓ₁} {ℓ₂} = refl
  {-# REWRITE stamp-val-assoc #-}

  stamp-pres : ∀ {T ℓ ζ} {V W : ∅ ⊢ᵛ T of ℓ}
    → (ℓ′ : ℒ)
    → T of ℓ ⦂ V ≈ᵛ⦅ ζ ⦆ W
    → T of (ℓ ⊔ ℓ′) ⦂ stamp-val V ℓ′ ≈ᵛ⦅ ζ ⦆ stamp-val W ℓ′
  stamp-pres {T = `𝔹} {ℓ} {V = V} {W = W} ℓ′ V≈W =
    λ ℓ⊔ℓ′⊑ζ → cong (λ X → stamp-val X ℓ′) (V≈W (⊑-trans ⊔-upper₁ ℓ⊔ℓ′⊑ζ))
  stamp-pres {T = (T₁ of ℓ₁) ⇒ (T₂ of ℓ₂)} {ζ = ζ} {V = ƛ N₁ of ℓ₃} {ƛ N₂ of .ℓ₃} ℓ₄ V≈W ℓ⊔ℓ′⊑ζ {V′} {W′} V′≈W′
    p₁ p₂ with p₁ | p₂
  ... | ⇓-app {V = V₁} ⇓-val ⇓-val N₁[V′]⇓V₁ | ⇓-app {V = W₁} ⇓-val ⇓-val N₂[W′]⇓W₁ =
    assoc≈
      (stamp-pres ℓ₄
        (V≈W (⊑-trans ⊔-upper₁ ℓ⊔ℓ′⊑ζ) V′≈W′
          (⇓-app ⇓-val ⇓-val N₁[V′]⇓V₁)
          (⇓-app ⇓-val ⇓-val N₂[W′]⇓W₁)))
    where
      assoc≈ :
          T₂ of ((ℓ₂ ⊔ ℓ₃) ⊔ ℓ₄) ⦂ stamp-val V₁ (ℓ₃ ⊔ ℓ₄) ≈ᵛ⦅ ζ ⦆ stamp-val W₁ (ℓ₃ ⊔ ℓ₄)
        → T₂ of (ℓ₂ ⊔ (ℓ₃ ⊔ ℓ₄)) ⦂ stamp-val V₁ (ℓ₃ ⊔ ℓ₄) ≈ᵛ⦅ ζ ⦆ stamp-val W₁ (ℓ₃ ⊔ ℓ₄)
      assoc≈ = subst (λ □ → T₂ of □ ⦂ stamp-val V₁ (ℓ₃ ⊔ ℓ₄) ≈ᵛ⦅ ζ ⦆ stamp-val W₁ (ℓ₃ ⊔ ℓ₄)) ⊔-assoc

  fundamental : ∀ {Γ T ℓ ζ} {σ₁ σ₂ : Γ →ˢ ∅}
    → (M : Γ ⊢ᵉ T of ℓ)
    → Γ ⊢ σ₁ ≈⦅ ζ ⦆ σ₂
      ------------------------------------------------
    → T of ℓ ⦂ (substᵉ σ₁ M) ≈ᵉ⦅ ζ ⦆ (substᵉ σ₂ M)
  fundamental (` x) σ₁≈σ₂ = σ₁≈σ₂ x
  fundamental (val ($ b of ℓ)) σ₁≈σ₂ ⇓-val ⇓-val _ = refl
  fundamental {T = (T₁ of ℓ₁) ⇒ (T₂ of ℓ₂)} {σ₁ = σ₁} {σ₂ = σ₂}
    (val (ƛ N of ℓ)) σ₁≈σ₂ ⇓-val ⇓-val =
      λ ℓ⊑ζ {V′} {W′} V′≈W′ →
        λ { (⇓-app ⇓-val ⇓-val N[V′]⇓V)
            (⇓-app ⇓-val ⇓-val N[W′]⇓W) →
              stamp-pres ℓ
                (fundamental N
                  (≈-• σ₁≈σ₂ (≈ᵛ→≈ᵉ V′≈W′))
                  (subst (λ □ → □ ⇓ _) (exts-sub-cons σ₁ N (val V′)) N[V′]⇓V)
                  (subst (λ □ → □ ⇓ _) (exts-sub-cons σ₂ N (val W′)) N[W′]⇓W))
          }
  fundamental (_`∧_ {ℓ₁ = ℓ₁} {ℓ₂} M N) σ₁≈σ₂
    (⇓-∧ M⇓V₁ N⇓W₁) (⇓-∧ M⇓V₂ N⇓W₂) =
      λ ℓ₁⊔ℓ₂⊑ζ →
        cong₂ _⟦∧⟧_
          (fundamental M σ₁≈σ₂ M⇓V₁ M⇓V₂ (⊑-trans ⊔-upper₁ ℓ₁⊔ℓ₂⊑ζ))
          (fundamental N σ₁≈σ₂ N⇓W₁ N⇓W₂ (⊑-trans ⊔-upper₂ ℓ₁⊔ℓ₂⊑ζ))
  fundamental (_`∨_ {ℓ₁ = ℓ₁} {ℓ₂} M N) σ₁≈σ₂
    (⇓-∨ M⇓V₁ N⇓W₁) (⇓-∨ M⇓V₂ N⇓W₂) =
      λ ℓ₁⊔ℓ₂⊑ζ →
        cong₂ _⟦∨⟧_
          (fundamental M σ₁≈σ₂ M⇓V₁ M⇓V₂ (⊑-trans ⊔-upper₁ ℓ₁⊔ℓ₂⊑ζ))
          (fundamental N σ₁≈σ₂ N⇓W₁ N⇓W₂ (⊑-trans ⊔-upper₂ ℓ₁⊔ℓ₂⊑ζ))
  fundamental {ζ = ζ} (_·_ {T = `𝔹} {ℓ₃ = ℓ₃} L M) σ₁≈σ₂
    (⇓-app L⇓₁ M⇓₁ N[V]⇓V₁) (⇓-app L⇓₂ M⇓₂ N[W]⇓W₁)
    with ℓ₃ ⊑? ζ
  ... | yes ℓ₃⊑ζ =
    fundamental L σ₁≈σ₂ L⇓₁ L⇓₂ ℓ₃⊑ζ
      (fundamental M σ₁≈σ₂ M⇓₁ M⇓₂)
      (⇓-app ⇓-val ⇓-val N[V]⇓V₁)
      (⇓-app ⇓-val ⇓-val N[W]⇓W₁)
  ... | no ¬ℓ₃⊑ζ =
    λ ℓ₂⊔ℓ₃⊑ζ → ⊥-elim (¬ℓ₃⊑ζ (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₃⊑ζ))
  fundamental {ζ = ζ} (_·_ {T = (T₄ of ℓ₄) ⇒ (T₅ of ℓ₅)} {ℓ₃ = ℓ₃} L M) σ₁≈σ₂
    (⇓-app L⇓₁ M⇓₁ N[V]⇓V₁) (⇓-app L⇓₂ M⇓₂ N[W]⇓W₁)
    with ℓ₃ ⊑? ζ
  ... | yes ℓ₃⊑ζ =
    fundamental L σ₁≈σ₂ L⇓₁ L⇓₂ ℓ₃⊑ζ
      (fundamental M σ₁≈σ₂ M⇓₁ M⇓₂)
      (⇓-app ⇓-val ⇓-val N[V]⇓V₁)
      (⇓-app ⇓-val ⇓-val N[W]⇓W₁)
  ... | no ¬ℓ₃⊑ζ =
    λ ℓ₂⊔ℓ₃⊑ζ → ⊥-elim (¬ℓ₃⊑ζ (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₃⊑ζ))
  fundamental (if_then_else_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L M N) σ₁≈σ₂
    (⇓-if-then L⇓true M⇓V₁) (⇓-if-then L⇓true′ M⇓V₂) =
      fundamental M σ₁≈σ₂ M⇓V₁ M⇓V₂
  fundamental {ζ = ζ} (if_then_else_ {T = `𝔹} {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L M N) σ₁≈σ₂
    (⇓-if-then L⇓true M⇓V₁) (⇓-if-else L⇓false N⇓W₂) =
      λ ℓ₂⊔ℓ₁⊑ζ →
        case fundamental L σ₁≈σ₂ L⇓true L⇓false (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₁⊑ζ) of λ ()
  fundamental {ζ = ζ} (if_then_else_ {T = (T₄ of ℓ₄) ⇒ (T₅ of ℓ₅)} {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L M N) σ₁≈σ₂
    (⇓-if-then L⇓true M⇓V₁) (⇓-if-else L⇓false N⇓W₂) =
      λ ℓ₂⊔ℓ₁⊑ζ →
        case fundamental L σ₁≈σ₂ L⇓true L⇓false (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₁⊑ζ) of λ ()
  fundamental {ζ = ζ} (if_then_else_ {T = `𝔹} {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L M N) σ₁≈σ₂
    (⇓-if-else L⇓false N⇓W₁) (⇓-if-then L⇓true M⇓V₂) =
      λ ℓ₂⊔ℓ₁⊑ζ →
        case fundamental L σ₁≈σ₂ L⇓false L⇓true (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₁⊑ζ) of λ ()
  fundamental {ζ = ζ} (if_then_else_ {T = (T₄ of ℓ₄) ⇒ (T₅ of ℓ₅)} {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L M N) σ₁≈σ₂
    (⇓-if-else L⇓false N⇓W₁) (⇓-if-then L⇓true M⇓V₂) =
      λ ℓ₂⊔ℓ₁⊑ζ →
        case fundamental L σ₁≈σ₂ L⇓false L⇓true (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₁⊑ζ) of λ ()
  fundamental (if_then_else_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L M N) σ₁≈σ₂
    (⇓-if-else L⇓false N⇓W₁) (⇓-if-else L⇓false′ N⇓W₂) =
      fundamental N σ₁≈σ₂ N⇓W₁ N⇓W₂
  fundamental (sub M A<:B) σ₁≈σ₂ ()
