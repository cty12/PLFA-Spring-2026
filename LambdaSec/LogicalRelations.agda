{-# OPTIONS --rewriting #-}

module LambdaSec.LogicalRelations where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Function using (case_of_)

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import LambdaSec.LabelLattice using (LabelLattice)

module λSec (𝑳 : LabelLattice) where

  open import LambdaSec.LambdaSec 𝑳 public

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
  ... | no ¬ℓ₃⊑ζ with T
  ...   | `𝔹               = λ ℓ₂⊔ℓ₃⊑ζ → contradiction (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₃⊑ζ) ¬ℓ₃⊑ζ
  ...   | _ of _ ⇒ _ of _ = λ ℓ₂⊔ℓ₃⊑ζ → contradiction (⊑-trans ⊔-upper₂ ℓ₂⊔ℓ₃⊑ζ) ¬ℓ₃⊑ζ
  fundamental (if_then_else_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L M N) γ
    (⇓-if-then L⇓true M⇓V₁) (⇓-if-then L⇓true′ M⇓V₂) =
      fundamental M γ M⇓V₁ M⇓V₂
  fundamental (if_then_else_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L M N) γ
    (⇓-if-else L⇓false N⇓W₁) (⇓-if-else L⇓false′ N⇓W₂) =
      fundamental N γ N⇓W₁ N⇓W₂
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
