{-# OPTIONS --rewriting #-}

module SystemFLogicalRelations where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
  renaming (subst to substEq)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)
  renaming (_,_ to ⟨_,_⟩)
open import Agda.Builtin.Unit using (⊤)
open import Function using (case_of_)
open import Level using (0ℓ; Lift; lift) renaming (suc to lsuc)

open import SystemFIntrinsic

Rel : Type ∅ → Type ∅ → Set₁
Rel A B = (V : ∅ ; ∅ ⊢ A) → (W : ∅ ; ∅ ⊢ B) → Value V → Value W → Set

-- Corresponds to Section 4.3's relational substitutions ρ,
-- with projections to the left type substitution, right type substitution,
-- and the relation assigned to each type variable.
-- In the lecture notes, D⟦ Δ ⟧ is the set of relational substitutions for Δ;
-- here, that role is played directly by RelSub Δ.
record RelSub (Δ : TyCtx) : Set₁ where
  field
    ρ₁ : Δ ⇒ˢ ∅
    ρ₂ : Δ ⇒ˢ ∅
    ρR : ∀ α → Rel (ρ₁ α) (ρ₂ α)

open RelSub public

-- Section 4.3's ρ[α ↦ (A₁ , A₂ , R)].
extendRelSub : ∀ {Δ}
  → (ρ : RelSub Δ)
  → (A₁ A₂ : Type ∅)
  → Rel A₁ A₂
  → RelSub (Δ ,α)
(extendRelSub ρ A₁ A₂ R) .ρ₁        = A₁ •ᵗ ρ₁ ρ
(extendRelSub ρ A₁ A₂ R) .ρ₂        = A₂ •ᵗ ρ₂ ρ
(extendRelSub ρ A₁ A₂ R) .ρR Z      = R
(extendRelSub ρ A₁ A₂ R) .ρR (S α)  = ρR ρ α

emptyRelSub : RelSub ∅
(emptyRelSub .ρ₁) = idᵗ
(emptyRelSub .ρ₂) = idᵗ
(emptyRelSub .ρR) ()

-- Section 4.3's V⟦ A ⟧ρ.
-- The type-variable case uses ρR, the function case substitutes related
-- values into lambda bodies, and the ∀ case substitutes related types
-- directly into type-abstraction bodies.
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
ValueRel `Nat ρ `zero `zero V-zero V-zero = Lift (lsuc 0ℓ) ⊤
ValueRel (A ⇒ B) ρ (ƛ _ ˙ N) (ƛ _ ˙ M) V-ƛ V-ƛ =
  ∀ {V W} (v : Value V) (w : Value W)
   → ValueRel A ρ V W v w
   → ExprRel B ρ (N [ V ]) (M [ W ])
ValueRel (A `× B) ρ (`⟨ V₁ , V₂ ⟩) (`⟨ W₁ , W₂ ⟩) (V-⟨⟩ v₁ v₂) (V-⟨⟩ w₁ w₂) =
  ValueRel A ρ V₁ W₁ v₁ w₁ × ValueRel B ρ V₂ W₂ v₂ w₂
ValueRel (`∀ A) ρ (Λ N) (Λ M) V-Λ V-Λ =
  ∀ (A₁ A₂ : Type ∅)
   → (R : Rel A₁ A₂)
   → ExprRel A (extendRelSub ρ A₁ A₂ R) (N [ A₁ ]ᵀ) (M [ A₂ ]ᵀ)

-- Section 4.3's E⟦ A ⟧ρ.
-- Expression relation: both terms reduce to values that are related
-- by the value interpretation.
ExprRel A ρ M N =
  ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
    (M —↠ V) × (N —↠ W) × ValueRel A ρ V W v w

-- Corresponds to G⟦ Γ ⟧ρ for open terms: two closing substitutions together
-- with proofs that corresponding variables are related values.
record RelEnv {Δ} (Γ : Ctx Δ) (ρ : RelSub Δ) : Set₁ where
  field
    γ₁ : substCtx (ρ₁ ρ) Γ →ˢ ∅
    γ₂ : substCtx (ρ₂ ρ) Γ →ˢ ∅
    γv₁ : ∀ {A} (x : Γ ∋ A) → Value (γ₁ (substᵗ-∋ (ρ₁ ρ) x))
    γv₂ : ∀ {A} (x : Γ ∋ A) → Value (γ₂ (substᵗ-∋ (ρ₂ ρ) x))
    γR : ∀ {A} (x : Γ ∋ A)
      → ValueRel A ρ (γ₁ (substᵗ-∋ (ρ₁ ρ) x)) (γ₂ (substᵗ-∋ (ρ₂ ρ) x)) (γv₁ x) (γv₂ x)

open RelEnv public

emptyRelEnv : ∀ {ρ : RelSub ∅} → RelEnv ∅ ρ
(emptyRelEnv .γ₁) = id
(emptyRelEnv .γ₂) = id
(emptyRelEnv .γv₁) ()
(emptyRelEnv .γv₂) ()
(emptyRelEnv .γR) ()

-- Open-term logical relation: for every relational substitution ρ and
-- relational environment γ, the two terms close to expressions related
-- by E⟦ A ⟧ρ.
LogicalRel : ∀ {Δ Γ A} → (M N : Δ ; Γ ⊢ A) → Set₁
LogicalRel {Δ} {Γ} {A} M N = ∀ (ρ : RelSub Δ) (γ : RelEnv Γ ρ)
  → ExprRel A ρ (subst (γ .γ₁) (substᵀ (ρ .ρ₁) M)) (subst (γ .γ₂) (substᵀ (ρ .ρ₂) N))

-- Fundamental Property (page 24): every well-typed term is related to itself.
postulate
  fundamental : ∀ {Δ Γ A} (M : Δ ; Γ ⊢ A) → LogicalRel M M

postulate
  close-empty-id : ∀ {A} (M : ∅ ; ∅ ⊢ A) → subst id (substᵀ idᵗ M) ≡ M

fundamental-id : ∀ (M : ∅ ; ∅ ⊢ `∀ (` Z ⇒ ` Z)) → ExprRel (`∀ (` Z ⇒ ` Z)) emptyRelSub M M
fundamental-id M = substEq
    (λ □ → ExprRel (`∀ (` Z ⇒ ` Z)) emptyRelSub □ □)
    (close-empty-id M)
    (fundamental M emptyRelSub emptyRelEnv)

singletonRel : ∀ {A B}
  → (V : ∅ ; ∅ ⊢ A)
  → (W : ∅ ; ∅ ⊢ B)
  → Rel A B
singletonRel V W V′ W′ _ _ = (V ≡ V′) × (W ≡ W′)

singletonRel-refl : ∀ {A} {V : ∅ ; ∅ ⊢ A}
  → (v : Value V)
  → ValueRel (` Z) (extendRelSub emptyRelSub A A (singletonRel V V)) V V v v
singletonRel-refl v = lift ⟨ refl , refl ⟩

-- Free Theorem (I), page 27.
free-theorem-id : ∀ {A : Type ∅}
  → (M : ∅ ; ∅ ⊢ `∀ (` Z ⇒ ` Z))
  → (V : ∅ ; ∅ ⊢ A)
  → Value V
    ------------------------
  → (M ∙ A) · V —↠ V
free-theorem-id {A} M V v =
  case fundamental-id M of λ where
  ⟨ Λ N₁ , ⟨ Λ N₂ , ⟨ V-Λ , ⟨ V-Λ , ⟨ M↠ΛN₁ , ⟨ M↠ΛN₂ , rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
    case rel A A (singletonRel V V) of λ where
    ⟨ ƛ _ ˙ N₁′ , ⟨ ƛ _ ˙ N₂′ , ⟨ V-ƛ , ⟨ V-ƛ , ⟨ N₁[A]↠ƛN₁′ , ⟨ N₂[A]↠ƛN₂′ , rel′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
      case rel′ v v (singletonRel-refl v) of λ where
      ⟨ W₁ , ⟨ W₂ , ⟨ w₁ , ⟨ w₂ , ⟨ N₁′[V]↠W₁ , ⟨ N₂′[V]↠W₂ , lift ⟨ refl , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ → 
        —↠-trans (·₁-↠ (∙-↠ M↠ΛN₁))
            (—↠-trans
              (((Λ N₁ ∙ A) · V) —→⟨ ξ-·₁ β-Λ ⟩ (((N₁ [ A ]ᵀ) · V) ∎))
                (—↠-trans
                  (·₁-↠ N₁[A]↠ƛN₁′)
                    (—↠-trans
                      (((ƛ _ ˙ N₁′) · V) —→⟨ β-ƛ v ⟩ ((N₁′ [ V ]) ∎)) N₁′[V]↠W₁)))


SwapTy : Type ∅
SwapTy = `∀ (`∀ ((` (S Z) `× ` Z) ⇒ (` Z `× ` (S Z))))

swap-inst : ∀ {A B}
  → (M : ∅ ; ∅ ⊢ SwapTy)
  → ∅ ; ∅ ⊢ ((A `× B) ⇒ (B `× A))
swap-inst {A} {B} M = (M ∙ A) ∙ B

fundamental-swap : ∀ (M : ∅ ; ∅ ⊢ SwapTy) → ExprRel SwapTy emptyRelSub M M
fundamental-swap M = substEq
    (λ □ → ExprRel SwapTy emptyRelSub □ □)
    (close-empty-id M)
    (fundamental M emptyRelSub emptyRelEnv)

swap-input-related : ∀ {A B}
  → {V : ∅ ; ∅ ⊢ A}
  → {W : ∅ ; ∅ ⊢ B}
  → (v : Value V)
  → (w : Value W)
  → ValueRel
      ((` (S Z)) `× (` Z))
      (extendRelSub (extendRelSub emptyRelSub A B (singletonRel V W)) B A (singletonRel W V))
      (`⟨ V , W ⟩) (`⟨ W , V ⟩) (V-⟨⟩ v w) (V-⟨⟩ w v)
swap-input-related v w = ⟨ lift ⟨ refl , refl ⟩ , lift ⟨ refl , refl ⟩ ⟩

-- For the swapped result, the polymorphic term must have type
-- ∀ α. ∀ β. α × β → β × α.
free-theorem-swap : ∀ {A B : Type ∅}
  → (M : ∅ ; ∅ ⊢ SwapTy)
  → (V : ∅ ; ∅ ⊢ A)
  → (W : ∅ ; ∅ ⊢ B)
  → Value V
  → Value W
    ---------------------------------------------
  → (swap-inst M · `⟨ V , W ⟩) —↠ `⟨ W , V ⟩
free-theorem-swap {A} {B} M V W v w =
  case fundamental-swap M of λ where
  ⟨ Λ N₁ , ⟨ Λ N₂ , ⟨ V-Λ , ⟨ V-Λ , ⟨ M↠ΛN₁ , ⟨ M↠ΛN₂ , rel₁ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
    case rel₁ A B (singletonRel V W) of λ where
    ⟨ Λ N₁′ , ⟨ Λ N₂′ , ⟨ V-Λ , ⟨ V-Λ , ⟨ N₁[A]↠ΛN₁′ , ⟨ N₂[B]↠ΛN₂′ , rel₂ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
      case rel₂ B A (singletonRel W V) of λ where
      ⟨ ƛ _ ˙ N₁″ , ⟨ ƛ _ ˙ N₂″ , ⟨ V-ƛ , ⟨ V-ƛ , ⟨ N₁′[B]↠ƛN₁″ , ⟨ N₂′[A]↠ƛN₂″ , rel₃ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
        case rel₃ (V-⟨⟩ v w) (V-⟨⟩ w v) (swap-input-related v w) of λ where
        ⟨ `⟨ X₁ , X₂ ⟩ , ⟨ `⟨ Y₁ , Y₂ ⟩ , ⟨ V-⟨⟩ x₁ x₂ , ⟨ V-⟨⟩ y₁ y₂
          , ⟨ N₁″[⟨V,W⟩]↠⟨X₁,X₂⟩ , ⟨ N₂″[⟨W,V⟩]↠⟨Y₁,Y₂⟩
          , ⟨ lift ⟨ refl , _ ⟩ , lift ⟨ refl , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ →
            —↠-trans (·₁-↠ (∙-↠ (∙-↠ M↠ΛN₁)))
              (—↠-trans
                ((((Λ N₁ ∙ A) ∙ B) · `⟨ V , W ⟩) —→⟨ ξ-·₁ (ξ-∙ β-Λ) ⟩ ((((N₁ [ A ]ᵀ) ∙ B) · `⟨ V , W ⟩) ∎))
                (—↠-trans
                  (·₁-↠ (∙-↠ N₁[A]↠ΛN₁′))
                  (—↠-trans
                    (((Λ N₁′ ∙ B) · `⟨ V , W ⟩) —→⟨ ξ-·₁ β-Λ ⟩ (((N₁′ [ B ]ᵀ) · `⟨ V , W ⟩) ∎))
                    (—↠-trans
                      (·₁-↠ N₁′[B]↠ƛN₁″)
                      (—↠-trans
                        (((ƛ _ ˙ N₁″) · `⟨ V , W ⟩) —→⟨ β-ƛ (V-⟨⟩ v w) ⟩ ((N₁″ [ `⟨ V , W ⟩ ]) ∎))
                        N₁″[⟨V,W⟩]↠⟨X₁,X₂⟩)))))
