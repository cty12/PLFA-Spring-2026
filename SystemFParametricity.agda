{-# OPTIONS --rewriting #-}

module SystemFParametricity where

open import Relation.Binary.PropositionalEquality
  using    (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to substEq)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Unit using (⊤; tt)
open import Level using (Lift; lift) renaming (suc to lsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

open import SystemFIntrinsic

Rel : ∀ {ℓ} → Set → Set → Set (lsuc ℓ)
Rel {ℓ} A B = A → B → Set ℓ

liftRel : ∀ {ℓ} {A B : Set} → (A → B → Set ℓ) → (A → B → Set (lsuc ℓ))
liftRel {ℓ} R x y = Lift (lsuc ℓ) (R x y)

TyRel : ∀ {ℓ Ξ} → Type Ξ → Type Ξ → Set (lsuc (lsuc ℓ))
TyRel {ℓ} {Ξ} A B = Rel {lsuc ℓ} (Ξ ; ∅ ⊢ A) (Ξ ; ∅ ⊢ B)

TySubstRel : ∀ {ℓ Ξ Δ} → (Δ ⇒ˢ Ξ) → (Δ ⇒ˢ Ξ) → Set (lsuc (lsuc ℓ))
TySubstRel {ℓ} τ₁ τ₂ = ∀ α → TyRel {ℓ} (τ₁ α) (τ₂ α)

substTyRel : ∀ {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
    → (A : Type Δ)
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → TyRel {ℓ} (substᵗ τ₁ A) (substᵗ τ₂ A)
substTyRel A rel  = λ z z₁ → Lift (lsuc _) TyCtx

extTySubstRel : ∀ {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
  → TySubstRel {ℓ} τ₁ τ₂
  → {A B : Type Ξ}
  → TyRel {ℓ} A B
  → TySubstRel {ℓ} (τ₁ ,ᵗ A) (τ₂ ,ᵗ B)
extTySubstRel τ₁~τ₂ A~B Z      = A~B
extTySubstRel τ₁~τ₂ A~B (S α)  = τ₁~τ₂ α

renameTySubstRel : ∀ {ℓ Ξ Δ₁ Δ₂} (ρ : Δ₁ ⇒ʳ Δ₂) {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
  → TySubstRel {ℓ} τ₁ τ₂
  → TySubstRel {ℓ} (λ α → τ₁ (ρ α)) (λ α → τ₂ (ρ α))
renameTySubstRel ρ τ₁~τ₂ α = τ₁~τ₂ (ρ α)

substᵗ-,ᵗ-⇑ᵗ-cancel : ∀ {Ξ Δ} (τ : Δ ⇒ˢ Ξ) (A : Type Ξ) (B : Type Δ)
  → substᵗ (τ ,ᵗ A) (⇑ᵗ B) ≡ substᵗ τ B
substᵗ-,ᵗ-⇑ᵗ-cancel τ A B
  rewrite substᵗ-renameᵗ S_ (τ ,ᵗ A) B = refl

subst-ext-point : ∀ {Ξ Δ₁ Δ₂} (σ : Δ₁ ⇒ˢ Δ₂) (τ : Δ₂ ⇒ˢ Ξ) (B : Type Ξ)
  → ∀ α → ((λ β → substᵗ τ (σ β)) ,ᵗ B) α ≡ substᵗ (τ ,ᵗ B) (extsᵗ σ α)
subst-ext-point σ τ B Z      = refl
subst-ext-point σ τ B (S α)  = sym (substᵗ-,ᵗ-⇑ᵗ-cancel τ B (σ α))

rename-ext-point : ∀ {Ξ Δ₁ Δ₂} (ρ : Δ₁ ⇒ʳ Δ₂) (τ : Δ₂ ⇒ˢ Ξ) (B : Type Ξ)
  → ∀ α → ((λ β → τ (ρ β)) ,ᵗ B) α ≡ (τ ,ᵗ B) (extᵗ ρ α)
rename-ext-point ρ τ B Z      = refl
rename-ext-point ρ τ B (S α)  = refl

substCtx-,ᵗ-⇑ᶜ-cancel : ∀ {Ξ Δ} (τ : Δ ⇒ˢ Ξ) (A : Type Ξ) (Γ : Ctx Δ)
  → substCtx (τ ,ᵗ A) (⇑ᶜ Γ) ≡ substCtx τ Γ
substCtx-,ᵗ-⇑ᶜ-cancel τ A ∅ = refl
substCtx-,ᵗ-⇑ᶜ-cancel τ A (Γ , B)
  rewrite substCtx-,ᵗ-⇑ᶜ-cancel τ A Γ
        | substᵗ-,ᵗ-⇑ᵗ-cancel τ A B = refl

inst∀ : ∀ {Ξ Δ} (C : Type (Δ ,α)) (τ : Δ ⇒ˢ Ξ) (A : Type Ξ)
  → Ξ ; ∅ ⊢ substᵗ τ (∀̇ C)
  → Ξ ; ∅ ⊢ substᵗ (τ ,ᵗ A) C
inst∀ C τ A M = substEq (_ ; ∅ ⊢_) (∀-[] C τ A) (M ∙ A)

subst-[] : ∀ {Ξ Δ} (A : Type (Δ ,α)) (τ : Δ ⇒ˢ Ξ) (B : Type Δ)
  → substᵗ τ (A [ B ]ᵗ) ≡ substᵗ (τ ,ᵗ substᵗ τ B) A
subst-[] A τ B = trans (substᵗ-[]ᵗ τ A B) (∀-[] A τ (substᵗ τ B))

mutual

  ValueRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
    → (A : Type Δ)
    → TySubstRel {ℓ} τ₁ τ₂
    → Ξ ; ∅ ⊢ substᵗ τ₁ A
    → Ξ ; ∅ ⊢ substᵗ τ₂ A
    → Set (lsuc (lsuc ℓ))
  ValueRel n (` α) τ₁~τ₂ V W =
    Value V × Value W × liftRel (τ₁~τ₂ α) V W
  ValueRel n {ℓ = ℓ} `Nat τ₁~τ₂ V W =
    Value V × Value W × Lift (lsuc (lsuc ℓ)) (V ≡ W)
  ValueRel n (A ⇒ B) τ₁~τ₂ V W =
    Value V × Value W ×
    (∀ {L M}
    → ValueRel n A τ₁~τ₂ L M
    → TermRel n B τ₁~τ₂ (V · L) (W · M))
  ValueRel zero {ℓ = ℓ} (∀̇ A) τ₁~τ₂ V W =
    Value V × Value W × Lift (lsuc (lsuc ℓ)) ⊤
  ValueRel (suc n) {ℓ = ℓ} {Ξ = Ξ} {Δ} {τ₁} {τ₂} (∀̇ A) τ₁~τ₂ V W =
    Value V × Value W ×
    (∀ {A₁ A₂ : Type Ξ}
    → (A₁~A₂ : TyRel {ℓ} A₁ A₂)
    → TermRel n A (extTySubstRel τ₁~τ₂ A₁~A₂) (inst∀ A τ₁ A₁ V) (inst∀ A τ₂ A₂ W))

  TermRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
    → (A : Type Δ)
    → TySubstRel {ℓ} τ₁ τ₂
    → Ξ ; ∅ ⊢ substᵗ τ₁ A
    → Ξ ; ∅ ⊢ substᵗ τ₂ A
    → Set (lsuc (lsuc ℓ))
  TermRel n A τ₁~τ₂ M N =
    ∃[ V ] ∃[ W ]
      (M —↠ V) × (N —↠ W) × ValueRel n A τ₁~τ₂ V W

ValueRel⇒TermRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ} (A : Type Δ)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → {V : Ξ ; ∅ ⊢ substᵗ τ₁ A}
  → {W : Ξ ; ∅ ⊢ substᵗ τ₂ A}
  → ValueRel n A τ₁~τ₂ V W
  → TermRel n A τ₁~τ₂ V W
ValueRel⇒TermRel n A τ₁~τ₂ VW = ⟨ _ , ⟨ _ , ⟨ _ ∎ , ⟨ _ ∎ , VW ⟩ ⟩ ⟩ ⟩

ValueRel-left : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ} (A : Type Δ)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → {V : Ξ ; ∅ ⊢ substᵗ τ₁ A}
  → {W : Ξ ; ∅ ⊢ substᵗ τ₂ A}
  → ValueRel n A τ₁~τ₂ V W
  → Value V
ValueRel-left n (` α) τ₁~τ₂ ⟨ vV , ⟨ _ , _ ⟩ ⟩ = vV
ValueRel-left n `Nat τ₁~τ₂ ⟨ vV , ⟨ _ , _ ⟩ ⟩ = vV
ValueRel-left n (A ⇒ B) τ₁~τ₂ ⟨ vV , ⟨ _ , _ ⟩ ⟩ = vV
ValueRel-left zero (∀̇ A) τ₁~τ₂ ⟨ vV , ⟨ _ , _ ⟩ ⟩ = vV
ValueRel-left (suc n) (∀̇ A) τ₁~τ₂ ⟨ vV , ⟨ _ , _ ⟩ ⟩ = vV

ValueRel-right : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ} (A : Type Δ)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → {V : Ξ ; ∅ ⊢ substᵗ τ₁ A}
  → {W : Ξ ; ∅ ⊢ substᵗ τ₂ A}
  → ValueRel n A τ₁~τ₂ V W
  → Value W
ValueRel-right n (` α) τ₁~τ₂ ⟨ _ , ⟨ vW , _ ⟩ ⟩ = vW
ValueRel-right n `Nat τ₁~τ₂ ⟨ _ , ⟨ vW , _ ⟩ ⟩ = vW
ValueRel-right n (A ⇒ B) τ₁~τ₂ ⟨ _ , ⟨ vW , _ ⟩ ⟩ = vW
ValueRel-right zero (∀̇ A) τ₁~τ₂ ⟨ _ , ⟨ vW , _ ⟩ ⟩ = vW
ValueRel-right (suc n) (∀̇ A) τ₁~τ₂ ⟨ _ , ⟨ vW , _ ⟩ ⟩ = vW

TermRel-anti-reduction : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
  → (A : Type Δ)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → {L L′ : Ξ ; ∅ ⊢ substᵗ τ₁ A}
  → {M M′ : Ξ ; ∅ ⊢ substᵗ τ₂ A}
  → L —↠ L′
  → M —↠ M′
  → TermRel n A τ₁~τ₂ L′ M′
  → TermRel n A τ₁~τ₂ L M
TermRel-anti-reduction n A τ₁~τ₂ L—↠L′ M—↠M′ ⟨ V , ⟨ W , ⟨ L′—↠V , ⟨ M′—↠W , VW ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ —↠-trans L—↠L′ L′—↠V , ⟨ —↠-trans M—↠M′ M′—↠W , VW ⟩ ⟩ ⟩ ⟩

transport-↠ : ∀ {Δ Γ X Y} (eq : X ≡ Y) {L N : Δ ; Γ ⊢ X}
  → L —↠ N
  → substEq (_ ; Γ ⊢_) eq L —↠ substEq (_ ; Γ ⊢_) eq N
transport-↠ refl L—↠N = L—↠N

Value-no-step : ∀ {Δ Γ A} {V : Δ ; Γ ⊢ A} {N}
  → Value V
  → V —→ N
  → ⊥
Value-no-step V-zero ()
Value-no-step V-ƛ ()
Value-no-step V-Λ ()

Value-—↠-inv : ∀ {Δ Γ A} {V N : Δ ; Γ ⊢ A}
  → Value V
  → V —↠ N
  → V ≡ N
Value-—↠-inv vV (V ∎) = refl
Value-—↠-inv vV (V —→⟨ V—→N ⟩ Vrest) = ⊥-elim (Value-no-step vV V—→N)

TermRel→ValueRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
  → (A : Type Δ)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → {V : Ξ ; ∅ ⊢ substᵗ τ₁ A}
  → {W : Ξ ; ∅ ⊢ substᵗ τ₂ A}
  → Value V
  → Value W
  → TermRel n A τ₁~τ₂ V W
  → ValueRel n A τ₁~τ₂ V W
TermRel→ValueRel n A τ₁~τ₂ vV vW
  ⟨ V′ , ⟨ W′ , ⟨ V—↠V′ , ⟨ W—↠W′ , V′W′ ⟩ ⟩ ⟩ ⟩
  rewrite Value-—↠-inv vV V—↠V′ | Value-—↠-inv vW W—↠W′ = V′W′

transport-Value : ∀ {Δ Γ X Y} (eq : X ≡ Y) {L : Δ ; Γ ⊢ X}
  → Value L
  → Value (substEq (_ ; Γ ⊢_) eq L)
transport-Value refl vL = vL

transport-ValueRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
  → (A : Type Δ)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → {L L′ : Ξ ; ∅ ⊢ substᵗ τ₁ A}
  → {M M′ : Ξ ; ∅ ⊢ substᵗ τ₂ A}
  → L ≡ L′
  → M ≡ M′
  → ValueRel n A τ₁~τ₂ L M
  → ValueRel n A τ₁~τ₂ L′ M′
transport-ValueRel n A τ₁~τ₂ refl refl VW = VW

transport-TermRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
  → (A : Type Δ)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → {L L′ : Ξ ; ∅ ⊢ substᵗ τ₁ A}
  → {M M′ : Ξ ; ∅ ⊢ substᵗ τ₂ A}
  → L ≡ L′
  → M ≡ M′
  → TermRel n A τ₁~τ₂ L M
  → TermRel n A τ₁~τ₂ L′ M′
transport-TermRel n A τ₁~τ₂ refl refl LM = LM

substEq-trans : ∀ {A : Set} {P : A → Set} {X Y Z : A}
  → (eq₁ : X ≡ Y)
  → (eq₂ : Y ≡ Z)
  → (u : P X)
  → substEq P eq₂ (substEq P eq₁ u) ≡ substEq P (trans eq₁ eq₂) u
substEq-trans refl refl u = refl

substEq-sym-cancel : ∀ {A : Set} {P : A → Set} {X Y : A}
  → (eq : X ≡ Y)
  → {u : P Y}
  → substEq P eq (substEq P (sym eq) u) ≡ u
substEq-sym-cancel refl = refl

substEq-cancel : ∀ {A : Set} {P : A → Set} {X Y : A}
  → (eq : X ≡ Y)
  → {u : P X}
  → substEq P (sym eq) (substEq P eq u) ≡ u
substEq-cancel refl = refl

sym-sym : ∀ {A : Set} {X Y : A}
  → (eq : X ≡ Y)
  → sym (sym eq) ≡ eq
sym-sym refl = refl

_≟TyVar_ : ∀ {Δ} → (α β : TyVar Δ) → Dec (α ≡ β)
Z ≟TyVar Z = yes refl
(Z) ≟TyVar (S β) = no λ ()
(S α) ≟TyVar Z = no λ ()
(S α) ≟TyVar (S β) with α ≟TyVar β
... | yes refl = yes refl
... | no α≢β = no λ { refl → α≢β refl }

_≟Type_ : ∀ {Δ} → (A B : Type Δ) → Dec (A ≡ B)
(` α) ≟Type (` β) with α ≟TyVar β
... | yes refl = yes refl
... | no α≢β = no λ { refl → α≢β refl }
(` α) ≟Type `Nat = no λ ()
(` α) ≟Type (B ⇒ C) = no λ ()
(` α) ≟Type (∀̇ B) = no λ ()
`Nat ≟Type (` β) = no λ ()
`Nat ≟Type `Nat = yes refl
`Nat ≟Type (B ⇒ C) = no λ ()
`Nat ≟Type (∀̇ B) = no λ ()
(A ⇒ B) ≟Type (` α) = no λ ()
(A ⇒ B) ≟Type `Nat = no λ ()
(A ⇒ B) ≟Type (C ⇒ D) with A ≟Type C | B ≟Type D
... | yes refl | yes refl = yes refl
... | no A≢C | _ = no λ { refl → A≢C refl }
... | _ | no B≢D = no λ { refl → B≢D refl }
(A ⇒ B) ≟Type (∀̇ C) = no λ ()
(∀̇ A) ≟Type (` α) = no λ ()
(∀̇ A) ≟Type `Nat = no λ ()
(∀̇ A) ≟Type (B ⇒ C) = no λ ()
(∀̇ A) ≟Type (∀̇ B) with A ≟Type B
... | yes refl = yes refl
... | no A≢B = no λ { refl → A≢B refl }

Type-≡-irrelevant : ∀ {Δ} {A B : Type Δ} → (p q : A ≡ B) → p ≡ q
Type-≡-irrelevant = Decidable⇒UIP.≡-irrelevant _≟Type_

σ₀ᵗ-point : ∀ {Ξ Δ} (τ : Δ ⇒ˢ Ξ) (B : Type Δ)
  → ∀ α → (τ ,ᵗ substᵗ τ B) α ≡ substᵗ τ (σ₀ᵗ B α)
σ₀ᵗ-point τ B Z      = refl
σ₀ᵗ-point τ B (S α)  = refl

σ₀ᵗ-comp-[] : ∀ {Ξ Δ} (A : Type (Δ ,α)) (τ : Δ ⇒ˢ Ξ) (B : Type Δ)
  → trans (substᵗ-cong A (σ₀ᵗ-point τ B)) (sym (substᵗ-comp (σ₀ᵗ B) τ A))
    ≡ sym (subst-[] A τ B)
σ₀ᵗ-comp-[] A τ B = Type-≡-irrelevant _ _

substᵗ-cong-sym-cancel : ∀ {Ξ Δ} (A : Type Δ) {τ τ′ : Δ ⇒ˢ Ξ}
  → (eq : ∀ α → τ α ≡ τ′ α)
  → {L : Ξ ; ∅ ⊢ substᵗ τ A}
  → substEq (_ ; ∅ ⊢_) (substᵗ-cong A (λ α → sym (eq α)))
      (substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq) L)
    ≡ L
substᵗ-cong-sym-cancel A eq {L}
  rewrite Type-≡-irrelevant
            (substᵗ-cong A (λ α → sym (eq α)))
            (sym (substᵗ-cong A eq))
  = substEq-cancel {P = _ ; ∅ ⊢_} (substᵗ-cong A eq)

ext-,ᵗ-cong-point : ∀ {Ξ Δ} {τ τ′ : Δ ⇒ˢ Ξ}
  → (eq : ∀ α → τ α ≡ τ′ α)
  → (B : Type Ξ)
  → ∀ α → (τ ,ᵗ B) α ≡ (τ′ ,ᵗ B) α
ext-,ᵗ-cong-point eq B Z      = refl
ext-,ᵗ-cong-point eq B (S α)  = eq α

app-substEq : ∀ {Ξ X X′ Y Y′}
  → (eqX : X ≡ X′)
  → (eqY : Y ≡ Y′)
  → {V : Ξ ; ∅ ⊢ X ⇒ Y}
  → {L : Ξ ; ∅ ⊢ X′}
  → substEq (_ ; ∅ ⊢_) eqY (V · substEq (_ ; ∅ ⊢_) (sym eqX) L)
    ≡ substEq (_ ; ∅ ⊢_) (cong₂ _⇒_ eqX eqY) V · L
app-substEq refl refl = refl

∀̇-injective : ∀ {Δ} {A B : Type (Δ ,α)}
  → ∀̇ A ≡ ∀̇ B
  → A ≡ B
∀̇-injective refl = refl

polyApp-substEq : ∀ {Ξ C D}
  → (eq : ∀̇ C ≡ ∀̇ D)
  → (B : Type Ξ)
  → {L : Ξ ; ∅ ⊢ ∀̇ C}
  → substEq (_ ; ∅ ⊢_) eq L ∙ B
    ≡ substEq (_ ; ∅ ⊢_) (cong (λ X → X [ B ]ᵗ) (∀̇-injective eq)) (L ∙ B)
polyApp-substEq refl B = refl

arrow-congTySubst : ∀ {Ξ Δ} (A B : Type Δ) {τ τ′ : Δ ⇒ˢ Ξ}
  → (eq : ∀ α → τ α ≡ τ′ α)
  → {V : Ξ ; ∅ ⊢ substᵗ τ (A ⇒ B)}
  → {L : Ξ ; ∅ ⊢ substᵗ τ′ A}
  → substEq (_ ; ∅ ⊢_) (substᵗ-cong B eq)
      (V · substEq (_ ; ∅ ⊢_) (substᵗ-cong A (λ α → sym (eq α))) L)
    ≡ substEq (_ ; ∅ ⊢_) (substᵗ-cong (A ⇒ B) eq) V · L
arrow-congTySubst A B {τ = τ} {τ′ = τ′} eq {V} {L} =
  trans
    (cong
      (λ e → substEq (_ ; ∅ ⊢_) eqB (V · substEq (_ ; ∅ ⊢_) e L))
      eqA-sym)
    (trans
      (app-substEq eqA eqB)
      (cong (λ e → substEq (_ ; ∅ ⊢_) e V · L) eq⇒))
  where
  eqA : substᵗ τ A ≡ substᵗ τ′ A
  eqA = substᵗ-cong A eq

  eqB : substᵗ τ B ≡ substᵗ τ′ B
  eqB = substᵗ-cong B eq

  eqA-sym : substᵗ-cong A (λ α → sym (eq α)) ≡ sym eqA
  eqA-sym = Type-≡-irrelevant _ _

  eq⇒ : cong₂ _⇒_ eqA eqB ≡ substᵗ-cong (A ⇒ B) eq
  eq⇒ = Type-≡-irrelevant _ _

inst∀-congTySubst : ∀ {Ξ Δ} (A : Type (Δ ,α)) {τ τ′ : Δ ⇒ˢ Ξ}
  → (eq : ∀ α → τ α ≡ τ′ α)
  → (B : Type Ξ)
  → {L : Ξ ; ∅ ⊢ substᵗ τ (∀̇ A)}
  → inst∀ A τ′ B (substEq (_ ; ∅ ⊢_) (substᵗ-cong (∀̇ A) eq) L)
    ≡ substEq (_ ; ∅ ⊢_) (substᵗ-cong A (ext-,ᵗ-cong-point eq B)) (inst∀ A τ B L)
inst∀-congTySubst A {τ = τ} {τ′} eq B {L} =
  trans
    (cong (substEq (_ ; ∅ ⊢_) (∀-[] A τ′ B))
      (polyApp-substEq (substᵗ-cong (∀̇ A) eq) B))
    (trans
      (substEq-trans
        (cong (λ X → X [ B ]ᵗ) (∀̇-injective (substᵗ-cong (∀̇ A) eq)))
        (∀-[] A τ′ B)
        (L ∙ B))
      (trans
        (cong (λ e → substEq (_ ; ∅ ⊢_) e (L ∙ B)) bodyEq)
        (sym (substEq-trans
          (∀-[] A τ B)
          (substᵗ-cong A (ext-,ᵗ-cong-point eq B))
          (L ∙ B)))))
  where
  bodyEq :
    trans (cong (λ X → X [ B ]ᵗ) (∀̇-injective (substᵗ-cong (∀̇ A) eq)))
          (∀-[] A τ′ B)
    ≡
    trans (∀-[] A τ B)
          (substᵗ-cong A (ext-,ᵗ-cong-point eq B))
  bodyEq = Type-≡-irrelevant _ _

substᵗ-polyApp↑ : ∀ {Ξ Δ₁ Δ₂} (σ : Δ₁ ⇒ˢ Δ₂) (τ : Δ₂ ⇒ˢ Ξ)
  → (A : Type (Δ₁ ,α))
  → (B : Type Ξ)
  → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ (σ α)) (∀̇ A)}
  → substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp (extsᵗ σ) (τ ,ᵗ B) A))
      (substEq (_ ; ∅ ⊢_) (substᵗ-cong A (subst-ext-point σ τ B))
        (L ∙ B))
    ≡ substEq (_ ; ∅ ⊢_)
        (cong (λ X → X [ B ]ᵗ) (∀̇-injective (sym (substᵗ-comp σ τ (∀̇ A)))))
        (L ∙ B)
substᵗ-polyApp↑ σ τ A B {L} =
  trans
    (substEq-trans
      (substᵗ-cong A (subst-ext-point σ τ B))
      (sym (substᵗ-comp (extsᵗ σ) (τ ,ᵗ B) A))
      (L ∙ B))
    step↑
  where
  bodyEq : trans (substᵗ-cong A (subst-ext-point σ τ B))
                  (sym (substᵗ-comp (extsᵗ σ) (τ ,ᵗ B) A))
    ≡ cong (λ X → X [ B ]ᵗ) (∀̇-injective (sym (substᵗ-comp σ τ (∀̇ A))))
  bodyEq = Type-≡-irrelevant _ _

  step↑ : substEq (_ ; ∅ ⊢_)
            (trans (substᵗ-cong A (subst-ext-point σ τ B))
                   (sym (substᵗ-comp (extsᵗ σ) (τ ,ᵗ B) A)))
            (L ∙ B)
       ≡ substEq (_ ; ∅ ⊢_)
            (cong (λ X → X [ B ]ᵗ) (∀̇-injective (sym (substᵗ-comp σ τ (∀̇ A)))))
            (L ∙ B)
  step↑ rewrite bodyEq = refl

substᵗ-inst∀↑ : ∀ {Ξ Δ₁ Δ₂} (σ : Δ₁ ⇒ˢ Δ₂) (τ : Δ₂ ⇒ˢ Ξ)
  → (A : Type (Δ₁ ,α))
  → (B : Type Ξ)
  → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ (σ α)) (∀̇ A)}
  → substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp (extsᵗ σ) (τ ,ᵗ B) A))
      (substEq (_ ; ∅ ⊢_) (substᵗ-cong A (subst-ext-point σ τ B))
        (inst∀ A (λ α → substᵗ τ (σ α)) B L))
    ≡ inst∀ (substᵗ (extsᵗ σ) A) τ B
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ (∀̇ A))) L)
substᵗ-inst∀↑ σ τ A B {L} =
  trans
    (cong
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp (extsᵗ σ) (τ ,ᵗ B) A)))
      (substEq-trans
        (∀-[] A (λ α → substᵗ τ (σ α)) B)
        (substᵗ-cong A (subst-ext-point σ τ B))
        (L ∙ B)))
    (trans
      step↑
      (sym
        (trans
          (cong
            (substEq (_ ; ∅ ⊢_) (∀-[] (substᵗ (extsᵗ σ) A) τ B))
            (polyApp-substEq (sym (substᵗ-comp σ τ (∀̇ A))) B))
          (substEq-trans
            (cong (λ X → X [ B ]ᵗ)
              (∀̇-injective (sym (substᵗ-comp σ τ (∀̇ A)))))
            (∀-[] (substᵗ (extsᵗ σ) A) τ B)
            (L ∙ B)))))
  where
  bodyEq :
    trans (trans (∀-[] A (λ α → substᵗ τ (σ α)) B)
                 (substᵗ-cong A (subst-ext-point σ τ B)))
          (sym (substᵗ-comp (extsᵗ σ) (τ ,ᵗ B) A))
    ≡
    trans
      (cong (λ X → X [ B ]ᵗ)
        (∀̇-injective (sym (substᵗ-comp σ τ (∀̇ A)))))
      (∀-[] (substᵗ (extsᵗ σ) A) τ B)
  bodyEq = Type-≡-irrelevant _ _

  step↑ : substEq (_ ; ∅ ⊢_)
            (sym (substᵗ-comp (extsᵗ σ) (τ ,ᵗ B) A))
            (substEq (_ ; ∅ ⊢_)
              (trans (∀-[] A (λ α → substᵗ τ (σ α)) B)
                     (substᵗ-cong A (subst-ext-point σ τ B)))
              (L ∙ B))
       ≡ substEq (_ ; ∅ ⊢_)
            (trans
              (cong (λ X → X [ B ]ᵗ)
                (∀̇-injective (sym (substᵗ-comp σ τ (∀̇ A)))))
              (∀-[] (substᵗ (extsᵗ σ) A) τ B))
            (L ∙ B)
  step↑ =
    trans
      (substEq-trans
        (trans (∀-[] A (λ α → substᵗ τ (σ α)) B)
               (substᵗ-cong A (subst-ext-point σ τ B)))
        (sym (substᵗ-comp (extsᵗ σ) (τ ,ᵗ B) A))
        (L ∙ B))
      (cong (λ e → substEq (_ ; ∅ ⊢_) e (L ∙ B)) bodyEq)

substᵗ-inst∀↓ : ∀ {Ξ Δ₁ Δ₂} (σ : Δ₁ ⇒ˢ Δ₂) (τ : Δ₂ ⇒ˢ Ξ)
  → (A : Type (Δ₁ ,α))
  → (B : Type Ξ)
  → {L : Ξ ; ∅ ⊢ substᵗ τ (substᵗ σ (∀̇ A))}
  → inst∀ A (λ α → substᵗ τ (σ α)) B
      (substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ (∀̇ A)) L)
    ≡ substEq (_ ; ∅ ⊢_) (substᵗ-cong A (λ α → sym (subst-ext-point σ τ B α)))
        (substEq (_ ; ∅ ⊢_) (substᵗ-comp (extsᵗ σ) (τ ,ᵗ B) A)
          (inst∀ (substᵗ (extsᵗ σ) A) τ B L))
substᵗ-inst∀↓ σ τ A B {L} =
  trans
    (sym leftCancel)
    (cong
      (λ X →
        substEq (_ ; ∅ ⊢_) c
          (substEq (_ ; ∅ ⊢_) p X))
      mid)
  where
  u = substᵗ-comp σ τ (∀̇ A)
  p = substᵗ-comp (extsᵗ σ) (τ ,ᵗ B) A
  q = substᵗ-cong A (subst-ext-point σ τ B)
  c = substᵗ-cong A (λ α → sym (subst-ext-point σ τ B α))

  rhsCancel :
    inst∀ (substᵗ (extsᵗ σ) A) τ B
      (substEq (_ ; ∅ ⊢_) (sym u)
        (substEq (_ ; ∅ ⊢_) u L))
    ≡ inst∀ (substᵗ (extsᵗ σ) A) τ B L
  rhsCancel =
    cong (inst∀ (substᵗ (extsᵗ σ) A) τ B)
      (substEq-cancel {P = _ ; ∅ ⊢_} u)

  mid :
    substEq (_ ; ∅ ⊢_) (sym p)
      (substEq (_ ; ∅ ⊢_) q
        (inst∀ A (λ α → substᵗ τ (σ α)) B
          (substEq (_ ; ∅ ⊢_) u L)))
    ≡ inst∀ (substᵗ (extsᵗ σ) A) τ B L
  mid =
    trans
      (substᵗ-inst∀↑ σ τ A B {L = substEq (_ ; ∅ ⊢_) u L})
      rhsCancel

  c-sym-q : c ≡ sym q
  c-sym-q = Type-≡-irrelevant _ _

  leftCancel :
    substEq (_ ; ∅ ⊢_) c
      (substEq (_ ; ∅ ⊢_) p
        (substEq (_ ; ∅ ⊢_) (sym p)
          (substEq (_ ; ∅ ⊢_) q
            (inst∀ A (λ α → substᵗ τ (σ α)) B
              (substEq (_ ; ∅ ⊢_) u L)))))
    ≡ inst∀ A (λ α → substᵗ τ (σ α)) B
        (substEq (_ ; ∅ ⊢_) u L)
  leftCancel =
    trans
      (cong
        (substEq (_ ; ∅ ⊢_) c)
        (substEq-sym-cancel {P = _ ; ∅ ⊢_} p))
      (trans
        (cong
          (λ e →
            substEq (_ ; ∅ ⊢_) e
              (substEq (_ ; ∅ ⊢_) q
                (inst∀ A (λ α → substᵗ τ (σ α)) B
                  (substEq (_ ; ∅ ⊢_) u L))))
          c-sym-q)
        (substEq-cancel {P = _ ; ∅ ⊢_} q))

mutual
  ValueRel-congTySubst : ∀ (n : Nat) {ℓ Ξ Δ}
    → (A : Type Δ)
    → {τ₁ τ₁′ τ₂ τ₂′ : Δ ⇒ˢ Ξ}
    → {ρ : TySubstRel {ℓ} τ₁ τ₂}
    → {ρ′ : TySubstRel {ℓ} τ₁′ τ₂′}
    → (eq₁ : ∀ α → τ₁ α ≡ τ₁′ α)
    → (eq₂ : ∀ α → τ₂ α ≡ τ₂′ α)
    → (ρ→ρ′ : ∀ α {L M}
        → ρ α L M
        → ρ′ α (substEq (_ ; ∅ ⊢_) (eq₁ α) L) (substEq (_ ; ∅ ⊢_) (eq₂ α) M))
    → (ρ′→ρ : ∀ α {L M}
        → ρ′ α L M
        → ρ α (substEq (_ ; ∅ ⊢_) (sym (eq₁ α)) L) (substEq (_ ; ∅ ⊢_) (sym (eq₂ α)) M))
    → {L : Ξ ; ∅ ⊢ substᵗ τ₁ A}
    → {M : Ξ ; ∅ ⊢ substᵗ τ₂ A}
    → {L′ : Ξ ; ∅ ⊢ substᵗ τ₁′ A}
    → {M′ : Ξ ; ∅ ⊢ substᵗ τ₂′ A}
    → L′ ≡ substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₁) L
    → M′ ≡ substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₂) M
    → ValueRel n A ρ L M
    → ValueRel n A ρ′ L′ M′
  ValueRel-congTySubst n (` α) eq₁ eq₂ ρ→ρ′ ρ′→ρ {L = L} {M} L′eq M′eq ⟨ vL , ⟨ vM , lift LM~ ⟩ ⟩
    rewrite L′eq | M′eq =
      ⟨ transport-Value (eq₁ α) vL
      , ⟨ transport-Value (eq₂ α) vM
        , lift (ρ→ρ′ α LM~) ⟩ ⟩
  ValueRel-congTySubst n `Nat eq₁ eq₂ ρ→ρ′ ρ′→ρ {L = L} {M} L′eq M′eq VW
    rewrite substᵗ-cong `Nat eq₁ | substᵗ-cong `Nat eq₂ | L′eq | M′eq = VW
  ValueRel-congTySubst n {Ξ = Ξ} (A ⇒ B) {τ₁′ = τ₁′} {τ₂′ = τ₂′} {ρ = ρ} {ρ′ = ρ′} eq₁ eq₂ ρ→ρ′ ρ′→ρ {L = V} {M = W} L′eq M′eq ⟨ vV , ⟨ vW , VW~ ⟩ ⟩
    rewrite L′eq | M′eq =
      ⟨ transport-Value (substᵗ-cong (A ⇒ B) eq₁) vV
      , ⟨ transport-Value (substᵗ-cong (A ⇒ B) eq₂) vW
        , body ⟩ ⟩
    where
    body : ∀ {L′ : Ξ ; ∅ ⊢ substᵗ τ₁′ A} {M′ : Ξ ; ∅ ⊢ substᵗ τ₂′ A}
      → ValueRel n A ρ′ L′ M′
      → TermRel n B ρ′
          (substEq (_ ; ∅ ⊢_) (substᵗ-cong (A ⇒ B) eq₁) V · L′)
          (substEq (_ ; ∅ ⊢_) (substᵗ-cong (A ⇒ B) eq₂) W · M′)
    body {L′} {M′} N~ =
      TermRel-congTySubst n B eq₁ eq₂ ρ→ρ′ ρ′→ρ
        (sym (arrow-congTySubst A B eq₁ {V = V} {L = L′}))
        (sym (arrow-congTySubst A B eq₂ {V = W} {L = M′}))
        (VW~ (transport-ValueRel n A ρ
          (cong (λ e → substEq (_ ; ∅ ⊢_) e L′) (sym eqA₁))
          (cong (λ e → substEq (_ ; ∅ ⊢_) e M′) (sym eqA₂))
          N↓))
      where
      eqA₁ : substᵗ-cong A (λ α → sym (eq₁ α)) ≡ sym (substᵗ-cong A eq₁)
      eqA₁ = Type-≡-irrelevant _ _

      eqA₂ : substᵗ-cong A (λ α → sym (eq₂ α)) ≡ sym (substᵗ-cong A eq₂)
      eqA₂ = Type-≡-irrelevant _ _

      ρ→ρ′′ : ∀ α {L M}
        → ρ α L M
        → ρ′ α (substEq (_ ; ∅ ⊢_) (sym (sym (eq₁ α))) L)
               (substEq (_ ; ∅ ⊢_) (sym (sym (eq₂ α))) M)
      ρ→ρ′′ α {L} {M} LM~
        rewrite sym-sym (eq₁ α) | sym-sym (eq₂ α) = ρ→ρ′ α LM~

      N↓ : ValueRel n A ρ
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-cong A eq₁)) L′)
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-cong A eq₂)) M′)
      N↓ = ValueRel-congTySubst n A
        (λ α → sym (eq₁ α))
        (λ α → sym (eq₂ α))
        ρ′→ρ
        ρ→ρ′′
        (cong (λ e → substEq (_ ; ∅ ⊢_) e L′) (sym eqA₁))
        (cong (λ e → substEq (_ ; ∅ ⊢_) e M′) (sym eqA₂))
        N~
  ValueRel-congTySubst zero {Ξ = Ξ} (∀̇ A) {τ₁′ = τ₁′} {τ₂′ = τ₂′} eq₁ eq₂ ρ→ρ′ ρ′→ρ {L = V} {M = W} L′eq M′eq ⟨ vV , ⟨ vW , u ⟩ ⟩
    rewrite L′eq | M′eq =
      ⟨ transport-Value (substᵗ-cong (∀̇ A) eq₁) vV
      , ⟨ transport-Value (substᵗ-cong (∀̇ A) eq₂) vW
        , u ⟩ ⟩
  ValueRel-congTySubst (suc n) {ℓ = ℓ} {Ξ = Ξ} (∀̇ A) {τ₁′ = τ₁′} {τ₂′ = τ₂′} {ρ = ρ} {ρ′ = ρ′}
    eq₁ eq₂ ρ→ρ′ ρ′→ρ {L = V} {M = W} L′eq M′eq ⟨ vV , ⟨ vW , VW~ ⟩ ⟩
    rewrite L′eq | M′eq =
      ⟨ transport-Value (substᵗ-cong (∀̇ A) eq₁) vV
      , ⟨ transport-Value (substᵗ-cong (∀̇ A) eq₂) vW
        , body ⟩ ⟩
    where
    body : ∀ {A₁ A₂ : Type Ξ}
      → (A₁~A₂ : TyRel {ℓ} A₁ A₂)
      → TermRel n A (extTySubstRel ρ′ A₁~A₂)
          (inst∀ A τ₁′ A₁ (substEq (_ ; ∅ ⊢_) (substᵗ-cong (∀̇ A) eq₁) V))
          (inst∀ A τ₂′ A₂ (substEq (_ ; ∅ ⊢_) (substᵗ-cong (∀̇ A) eq₂) W))
    body {A₁} {A₂} A₁~A₂ =
      TermRel-congTySubst n A
        (ext-,ᵗ-cong-point eq₁ A₁)
        (ext-,ᵗ-cong-point eq₂ A₂)
        extρ→ρ′
        extρ′→ρ
        (inst∀-congTySubst A eq₁ A₁)
        (inst∀-congTySubst A eq₂ A₂)
        (VW~ A₁~A₂)
      where
      extρ→ρ′ : ∀ α {L M}
        → extTySubstRel ρ A₁~A₂ α L M
        → extTySubstRel ρ′ A₁~A₂ α
            (substEq (_ ; ∅ ⊢_) (ext-,ᵗ-cong-point eq₁ A₁ α) L)
            (substEq (_ ; ∅ ⊢_) (ext-,ᵗ-cong-point eq₂ A₂ α) M)
      extρ→ρ′ Z LM~ = LM~
      extρ→ρ′ (S α) LM~ = ρ→ρ′ α LM~

      extρ′→ρ : ∀ α {L M}
        → extTySubstRel ρ′ A₁~A₂ α L M
        → extTySubstRel ρ A₁~A₂ α
            (substEq (_ ; ∅ ⊢_) (sym (ext-,ᵗ-cong-point eq₁ A₁ α)) L)
            (substEq (_ ; ∅ ⊢_) (sym (ext-,ᵗ-cong-point eq₂ A₂ α)) M)
      extρ′→ρ Z LM~ = LM~
      extρ′→ρ (S α) LM~ = ρ′→ρ α LM~

  TermRel-congTySubst : ∀ (n : Nat) {ℓ Ξ Δ}
    → (A : Type Δ)
    → {τ₁ τ₁′ τ₂ τ₂′ : Δ ⇒ˢ Ξ}
    → {ρ : TySubstRel {ℓ} τ₁ τ₂}
    → {ρ′ : TySubstRel {ℓ} τ₁′ τ₂′}
    → (eq₁ : ∀ α → τ₁ α ≡ τ₁′ α)
    → (eq₂ : ∀ α → τ₂ α ≡ τ₂′ α)
    → (ρ→ρ′ : ∀ α {L M}
        → ρ α L M
        → ρ′ α (substEq (_ ; ∅ ⊢_) (eq₁ α) L) (substEq (_ ; ∅ ⊢_) (eq₂ α) M))
    → (ρ′→ρ : ∀ α {L M}
        → ρ′ α L M
        → ρ α (substEq (_ ; ∅ ⊢_) (sym (eq₁ α)) L) (substEq (_ ; ∅ ⊢_) (sym (eq₂ α)) M))
    → {L : Ξ ; ∅ ⊢ substᵗ τ₁ A}
    → {M : Ξ ; ∅ ⊢ substᵗ τ₂ A}
    → {L′ : Ξ ; ∅ ⊢ substᵗ τ₁′ A}
    → {M′ : Ξ ; ∅ ⊢ substᵗ τ₂′ A}
    → L′ ≡ substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₁) L
    → M′ ≡ substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₂) M
    → TermRel n A ρ L M
    → TermRel n A ρ′ L′ M′
  TermRel-congTySubst n A eq₁ eq₂ ρ→ρ′ ρ′→ρ {L = L} {M} L′eq M′eq ⟨ V , ⟨ W , ⟨ L—↠V , ⟨ M—↠W , VW ⟩ ⟩ ⟩ ⟩
    rewrite L′eq | M′eq =
      ⟨ substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₁) V
      , ⟨ substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₂) W
        , ⟨ transport-↠ (substᵗ-cong A eq₁) L—↠V
          , ⟨ transport-↠ (substᵗ-cong A eq₂) M—↠W
            , ValueRel-congTySubst n A eq₁ eq₂ ρ→ρ′ ρ′→ρ refl refl VW
            ⟩ ⟩ ⟩ ⟩

renameᵗ-inst∀↑ : ∀ {Ξ Δ₁ Δ₂} (ρ : Δ₁ ⇒ʳ Δ₂) (τ : Δ₂ ⇒ˢ Ξ)
  → (A : Type (Δ₁ ,α))
  → (B : Type Ξ)
  → {L : Ξ ; ∅ ⊢ substᵗ (λ α → τ (ρ α)) (∀̇ A)}
  → substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ (extᵗ ρ) (τ ,ᵗ B) A))
      (substEq (_ ; ∅ ⊢_) (substᵗ-cong A (rename-ext-point ρ τ B))
        (inst∀ A (λ α → τ (ρ α)) B L))
    ≡ inst∀ (renameᵗ (extᵗ ρ) A) τ B
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ (∀̇ A))) L)
renameᵗ-inst∀↑ ρ τ A B {L} =
  trans
    (cong
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ (extᵗ ρ) (τ ,ᵗ B) A)))
      (substEq-trans
        (∀-[] A (λ α → τ (ρ α)) B)
        (substᵗ-cong A (rename-ext-point ρ τ B))
        (L ∙ B)))
    (trans
      (substEq-trans
        (trans (∀-[] A (λ α → τ (ρ α)) B)
               (substᵗ-cong A (rename-ext-point ρ τ B)))
        (sym (substᵗ-renameᵗ (extᵗ ρ) (τ ,ᵗ B) A))
        (L ∙ B))
      (trans
        step-inst∀↑
        (sym
          (trans
            (cong
              (substEq (_ ; ∅ ⊢_) (∀-[] (renameᵗ (extᵗ ρ) A) τ B))
              (polyApp-substEq (sym (substᵗ-renameᵗ ρ τ (∀̇ A))) B))
            (substEq-trans
              (cong (λ X → X [ B ]ᵗ)
                (∀̇-injective (sym (substᵗ-renameᵗ ρ τ (∀̇ A)))))
              (∀-[] (renameᵗ (extᵗ ρ) A) τ B)
              (L ∙ B))))))
  where
  bodyEq :
    trans (trans (∀-[] A (λ α → τ (ρ α)) B)
                 (substᵗ-cong A (rename-ext-point ρ τ B)))
          (sym (substᵗ-renameᵗ (extᵗ ρ) (τ ,ᵗ B) A))
    ≡
    trans
      (cong (λ X → X [ B ]ᵗ)
        (∀̇-injective (sym (substᵗ-renameᵗ ρ τ (∀̇ A)))))
      (∀-[] (renameᵗ (extᵗ ρ) A) τ B)
  bodyEq = Type-≡-irrelevant _ _

  step-inst∀↑ : substEq (_ ; ∅ ⊢_)
            (trans (trans (∀-[] A (λ α → τ (ρ α)) B)
                         (substᵗ-cong A (rename-ext-point ρ τ B)))
                   (sym (substᵗ-renameᵗ (extᵗ ρ) (τ ,ᵗ B) A)))
            (L ∙ B)
       ≡ substEq (_ ; ∅ ⊢_)
            (trans
              (cong (λ X → X [ B ]ᵗ)
                (∀̇-injective (sym (substᵗ-renameᵗ ρ τ (∀̇ A)))))
              (∀-[] (renameᵗ (extᵗ ρ) A) τ B))
            (L ∙ B)
  step-inst∀↑ rewrite bodyEq = refl

renameᵗ-inst∀↓ : ∀ {Ξ Δ₁ Δ₂} (ρ : Δ₁ ⇒ʳ Δ₂) (τ : Δ₂ ⇒ˢ Ξ)
  → (A : Type (Δ₁ ,α))
  → (B : Type Ξ)
  → {L : Ξ ; ∅ ⊢ substᵗ τ (∀̇ (renameᵗ (extᵗ ρ) A))}
  → inst∀ A (λ α → τ (ρ α)) B
      (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ (∀̇ A)) L)
    ≡ substEq (_ ; ∅ ⊢_) (substᵗ-cong A (λ α → sym (rename-ext-point ρ τ B α)))
        (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ (extᵗ ρ) (τ ,ᵗ B) A)
          (inst∀ (renameᵗ (extᵗ ρ) A) τ B L))
renameᵗ-inst∀↓ ρ τ A B {L} =
  trans
    (sym leftCancel)
    (cong
      (λ X →
        substEq (_ ; ∅ ⊢_) c
          (substEq (_ ; ∅ ⊢_) p X))
      mid)
  where
  u = substᵗ-renameᵗ ρ τ (∀̇ A)
  p = substᵗ-renameᵗ (extᵗ ρ) (τ ,ᵗ B) A
  q = substᵗ-cong A (rename-ext-point ρ τ B)
  c = substᵗ-cong A (λ α → sym (rename-ext-point ρ τ B α))

  rhsCancel :
    inst∀ (renameᵗ (extᵗ ρ) A) τ B
      (substEq (_ ; ∅ ⊢_) (sym u)
        (substEq (_ ; ∅ ⊢_) u L))
    ≡ inst∀ (renameᵗ (extᵗ ρ) A) τ B L
  rhsCancel =
    cong (inst∀ (renameᵗ (extᵗ ρ) A) τ B)
      (substEq-cancel {P = _ ; ∅ ⊢_} u)

  mid :
    substEq (_ ; ∅ ⊢_) (sym p)
      (substEq (_ ; ∅ ⊢_) q
        (inst∀ A (λ α → τ (ρ α)) B
          (substEq (_ ; ∅ ⊢_) u L)))
    ≡ inst∀ (renameᵗ (extᵗ ρ) A) τ B L
  mid =
    trans
      (renameᵗ-inst∀↑ ρ τ A B {L = substEq (_ ; ∅ ⊢_) u L})
      rhsCancel

  c-sym-q : c ≡ sym q
  c-sym-q = Type-≡-irrelevant _ _

  leftCancel :
    substEq (_ ; ∅ ⊢_) c
      (substEq (_ ; ∅ ⊢_) p
        (substEq (_ ; ∅ ⊢_) (sym p)
          (substEq (_ ; ∅ ⊢_) q
            (inst∀ A (λ α → τ (ρ α)) B
              (substEq (_ ; ∅ ⊢_) u L)))))
    ≡ inst∀ A (λ α → τ (ρ α)) B
        (substEq (_ ; ∅ ⊢_) u L)
  leftCancel =
    trans
      (cong
        (substEq (_ ; ∅ ⊢_) c)
        (substEq-sym-cancel {P = _ ; ∅ ⊢_} p))
      (trans
        (cong
          (λ e →
            substEq (_ ; ∅ ⊢_) e
              (substEq (_ ; ∅ ⊢_) q
                (inst∀ A (λ α → τ (ρ α)) B
                  (substEq (_ ; ∅ ⊢_) u L))))
          c-sym-q)
        (substEq-cancel {P = _ ; ∅ ⊢_} q))

mutual
  renameᵗ-ValueRel↑ : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} (ρ : Δ₁ ⇒ʳ Δ₂) {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
    → (A : Type Δ₁)
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → {L : Ξ ; ∅ ⊢ substᵗ (λ α → τ₁ (ρ α)) A}
    → {M : Ξ ; ∅ ⊢ substᵗ (λ α → τ₂ (ρ α)) A}
    → ValueRel n A (renameTySubstRel ρ τ₁~τ₂) L M
    → ValueRel n (renameᵗ ρ A) τ₁~τ₂
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₁ A)) L)
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₂ A)) M)
  renameᵗ-ValueRel↑ n ρ {τ₁ = τ₁} {τ₂ = τ₂} (` α) τ₁~τ₂
    ⟨ vL , ⟨ vM , lift LM~ ⟩ ⟩
    rewrite substᵗ-renameᵗ ρ τ₁ (` α) | substᵗ-renameᵗ ρ τ₂ (` α) =
      ⟨ vL , ⟨ vM , lift LM~ ⟩ ⟩
  renameᵗ-ValueRel↑ n ρ {τ₁ = τ₁} {τ₂ = τ₂} `Nat τ₁~τ₂ VW
    rewrite substᵗ-renameᵗ ρ τ₁ `Nat | substᵗ-renameᵗ ρ τ₂ `Nat = VW
  renameᵗ-ValueRel↑ n {Ξ = Ξ} ρ {τ₁ = τ₁} {τ₂ = τ₂} (A ⇒ B) τ₁~τ₂ VW = go VW
    where
      go : ∀ {L : Ξ ; ∅ ⊢ substᵗ (λ α → τ₁ (ρ α)) (A ⇒ B)}
               {M : Ξ ; ∅ ⊢ substᵗ (λ α → τ₂ (ρ α)) (A ⇒ B)}
        → ValueRel n (A ⇒ B) (renameTySubstRel ρ τ₁~τ₂) L M
        → ValueRel n (renameᵗ ρ (A ⇒ B)) τ₁~τ₂
            (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₁ (A ⇒ B))) L)
            (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₂ (A ⇒ B))) M)
      go {L} {M} ⟨ vV , ⟨ vW , VW~ ⟩ ⟩ =
        ⟨ transport-Value (sym (substᵗ-renameᵗ ρ τ₁ (A ⇒ B))) vV
        , ⟨ transport-Value (sym (substᵗ-renameᵗ ρ τ₂ (A ⇒ B))) vW
          , body ⟩ ⟩
        where
          eqA₁ = substᵗ-renameᵗ ρ τ₁ A
          eqA₂ = substᵗ-renameᵗ ρ τ₂ A
          eqB₁ = substᵗ-renameᵗ ρ τ₁ B
          eqB₂ = substᵗ-renameᵗ ρ τ₂ B
          eq⇒₁ = substᵗ-renameᵗ ρ τ₁ (A ⇒ B)
          eq⇒₂ = substᵗ-renameᵗ ρ τ₂ (A ⇒ B)

          eq⇒-arr₁ : cong₂ _⇒_ (sym eqA₁) (sym eqB₁) ≡ sym eq⇒₁
          eq⇒-arr₁ = Type-≡-irrelevant _ _

          eq⇒-arr₂ : cong₂ _⇒_ (sym eqA₂) (sym eqB₂) ≡ sym eq⇒₂
          eq⇒-arr₂ = Type-≡-irrelevant _ _

          leftEq : ∀ {L' : Ξ ; ∅ ⊢ substᵗ τ₁ (renameᵗ ρ A)}
            → substEq (_ ; ∅ ⊢_) (sym eqB₁) (L · substEq (_ ; ∅ ⊢_) eqA₁ L')
              ≡ substEq (_ ; ∅ ⊢_) (sym eq⇒₁) L · L'
          leftEq {L'} =
            trans
              (sym (cong
                (λ e → substEq (_ ; ∅ ⊢_) (sym eqB₁) (L · substEq (_ ; ∅ ⊢_) e L'))
                (sym-sym eqA₁)))
              (trans
                (app-substEq (sym eqA₁) (sym eqB₁))
                (cong (λ e → substEq (_ ; ∅ ⊢_) e L · L') eq⇒-arr₁))

          rightEq : ∀ {M' : Ξ ; ∅ ⊢ substᵗ τ₂ (renameᵗ ρ A)}
            → substEq (_ ; ∅ ⊢_) (sym eqB₂) (M · substEq (_ ; ∅ ⊢_) eqA₂ M')
              ≡ substEq (_ ; ∅ ⊢_) (sym eq⇒₂) M · M'
          rightEq {M'} =
            trans
              (sym (cong
                (λ e → substEq (_ ; ∅ ⊢_) (sym eqB₂) (M · substEq (_ ; ∅ ⊢_) e M'))
                (sym-sym eqA₂)))
              (trans
                (app-substEq (sym eqA₂) (sym eqB₂))
                (cong (λ e → substEq (_ ; ∅ ⊢_) e M · M') eq⇒-arr₂))

          body : ∀ {L' : Ξ ; ∅ ⊢ substᵗ τ₁ (renameᵗ ρ A)}
                   {M' : Ξ ; ∅ ⊢ substᵗ τ₂ (renameᵗ ρ A)}
            → ValueRel n (renameᵗ ρ A) τ₁~τ₂ L' M'
            → TermRel n (renameᵗ ρ B) τ₁~τ₂
                (substEq (_ ; ∅ ⊢_) (sym eq⇒₁) L · L')
                (substEq (_ ; ∅ ⊢_) (sym eq⇒₂) M · M')
          body {L'} {M'} N~ =
            transport-TermRel n (renameᵗ ρ B) τ₁~τ₂ leftEq rightEq
              (renameᵗ-TermRel↑ n ρ B τ₁~τ₂
                (VW~ (renameᵗ-ValueRel↓ n ρ A τ₁~τ₂ N~)))
  renameᵗ-ValueRel↑ zero ρ {τ₁ = τ₁} {τ₂ = τ₂} (∀̇ A) τ₁~τ₂ VW = go VW
    where
      go : ∀ {L M} → ValueRel zero (∀̇ A) (renameTySubstRel ρ τ₁~τ₂) L M
        → ValueRel zero (renameᵗ ρ (∀̇ A)) τ₁~τ₂
            (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₁ (∀̇ A))) L)
            (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₂ (∀̇ A))) M)
      go ⟨ vV , ⟨ vW , u ⟩ ⟩ =
        ⟨ transport-Value (sym (substᵗ-renameᵗ ρ τ₁ (∀̇ A))) vV
        , ⟨ transport-Value (sym (substᵗ-renameᵗ ρ τ₂ (∀̇ A))) vW
          , u ⟩ ⟩
  renameᵗ-ValueRel↑ (suc n) {Ξ = Ξ} ρ {τ₁ = τ₁} {τ₂ = τ₂} (∀̇ A) τ₁~τ₂ {L} {M}
    ⟨ vL , ⟨ vM , LM~ ⟩ ⟩ =
      ⟨ transport-Value (sym (substᵗ-renameᵗ ρ τ₁ (∀̇ A))) vL
      , ⟨ transport-Value (sym (substᵗ-renameᵗ ρ τ₂ (∀̇ A))) vM
        , body ⟩ ⟩
    where
    body : ∀ {A₁ A₂ : Type Ξ}
      → (A₁~A₂ : TyRel A₁ A₂)
      → TermRel n (renameᵗ (extᵗ ρ) A) (extTySubstRel τ₁~τ₂ A₁~A₂)
          (inst∀ (renameᵗ (extᵗ ρ) A) τ₁ A₁
            (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₁ (∀̇ A))) L))
          (inst∀ (renameᵗ (extᵗ ρ) A) τ₂ A₂
            (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₂ (∀̇ A))) M))
    body {A₁} {A₂} A₁~A₂ =
      transport-TermRel n (renameᵗ (extᵗ ρ) A) (extTySubstRel τ₁~τ₂ A₁~A₂)
        (renameᵗ-inst∀↑ ρ τ₁ A A₁)
        (renameᵗ-inst∀↑ ρ τ₂ A A₂)
        (renameᵗ-TermRel↑ n (extᵗ ρ) A (extTySubstRel τ₁~τ₂ A₁~A₂) mid)
      where
      eq₁ : ∀ α → ((λ β → τ₁ (ρ β)) ,ᵗ A₁) α ≡ (τ₁ ,ᵗ A₁) (extᵗ ρ α)
      eq₁ = rename-ext-point ρ τ₁ A₁

      eq₂ : ∀ α → ((λ β → τ₂ (ρ β)) ,ᵗ A₂) α ≡ (τ₂ ,ᵗ A₂) (extᵗ ρ α)
      eq₂ = rename-ext-point ρ τ₂ A₂

      ρ→ρ' : ∀ α {V W}
        → extTySubstRel (renameTySubstRel ρ τ₁~τ₂) A₁~A₂ α V W
        → renameTySubstRel (extᵗ ρ) (extTySubstRel τ₁~τ₂ A₁~A₂) α
            (substEq (_ ; ∅ ⊢_) (eq₁ α) V)
            (substEq (_ ; ∅ ⊢_) (eq₂ α) W)
      ρ→ρ' Z VW = VW
      ρ→ρ' (S α) VW = VW

      ρ'→ρ : ∀ α {V W}
        → renameTySubstRel (extᵗ ρ) (extTySubstRel τ₁~τ₂ A₁~A₂) α V W
        → extTySubstRel (renameTySubstRel ρ τ₁~τ₂) A₁~A₂ α
            (substEq (_ ; ∅ ⊢_) (sym (eq₁ α)) V)
            (substEq (_ ; ∅ ⊢_) (sym (eq₂ α)) W)
      ρ'→ρ Z VW = VW
      ρ'→ρ (S α) VW = VW

      mid : TermRel n A
        (renameTySubstRel (extᵗ ρ) (extTySubstRel τ₁~τ₂ A₁~A₂))
        (substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₁)
          (inst∀ A (λ β → τ₁ (ρ β)) A₁ L))
        (substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₂)
          (inst∀ A (λ β → τ₂ (ρ β)) A₂ M))
      mid =
        TermRel-congTySubst n A eq₁ eq₂ ρ→ρ' ρ'→ρ refl refl
          (LM~ A₁~A₂)

  renameᵗ-ValueRel↓ : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} (ρ : Δ₁ ⇒ʳ Δ₂) {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
    → (A : Type Δ₁)
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → {L : Ξ ; ∅ ⊢ substᵗ τ₁ (renameᵗ ρ A)}
    → {M : Ξ ; ∅ ⊢ substᵗ τ₂ (renameᵗ ρ A)}
    → ValueRel n (renameᵗ ρ A) τ₁~τ₂ L M
    → ValueRel n A (renameTySubstRel ρ τ₁~τ₂)
        (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₁ A) L)
        (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₂ A) M)
  renameᵗ-ValueRel↓ n ρ {τ₁ = τ₁} {τ₂ = τ₂} (` α) τ₁~τ₂
    ⟨ vL , ⟨ vM , lift LM~ ⟩ ⟩
    rewrite substᵗ-renameᵗ ρ τ₁ (` α) | substᵗ-renameᵗ ρ τ₂ (` α) =
      ⟨ vL , ⟨ vM , lift LM~ ⟩ ⟩
  renameᵗ-ValueRel↓ n ρ {τ₁ = τ₁} {τ₂ = τ₂} `Nat τ₁~τ₂ VW
    rewrite substᵗ-renameᵗ ρ τ₁ `Nat | substᵗ-renameᵗ ρ τ₂ `Nat = VW
  renameᵗ-ValueRel↓ n {Ξ = Ξ} ρ {τ₁ = τ₁} {τ₂ = τ₂} (A ⇒ B) τ₁~τ₂ VW = go VW
    where
      go : ∀ {L : Ξ ; ∅ ⊢ substᵗ τ₁ (renameᵗ ρ (A ⇒ B))}
               {M : Ξ ; ∅ ⊢ substᵗ τ₂ (renameᵗ ρ (A ⇒ B))}
        → ValueRel n (renameᵗ ρ (A ⇒ B)) τ₁~τ₂ L M
        → ValueRel n (A ⇒ B) (renameTySubstRel ρ τ₁~τ₂)
            (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₁ (A ⇒ B)) L)
            (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₂ (A ⇒ B)) M)
      go {L} {M} ⟨ vV , ⟨ vW , VW~ ⟩ ⟩ =
        ⟨ transport-Value (substᵗ-renameᵗ ρ τ₁ (A ⇒ B)) vV
        , ⟨ transport-Value (substᵗ-renameᵗ ρ τ₂ (A ⇒ B)) vW
          , body ⟩ ⟩
        where
          eqA₁ = substᵗ-renameᵗ ρ τ₁ A
          eqA₂ = substᵗ-renameᵗ ρ τ₂ A
          eqB₁ = substᵗ-renameᵗ ρ τ₁ B
          eqB₂ = substᵗ-renameᵗ ρ τ₂ B
          eq⇒₁ = substᵗ-renameᵗ ρ τ₁ (A ⇒ B)
          eq⇒₂ = substᵗ-renameᵗ ρ τ₂ (A ⇒ B)

          eq⇒-arr₁ : cong₂ _⇒_ eqA₁ eqB₁ ≡ eq⇒₁
          eq⇒-arr₁ = Type-≡-irrelevant _ _

          eq⇒-arr₂ : cong₂ _⇒_ eqA₂ eqB₂ ≡ eq⇒₂
          eq⇒-arr₂ = Type-≡-irrelevant _ _

          leftEq : ∀ {L' : Ξ ; ∅ ⊢ substᵗ (λ α → τ₁ (ρ α)) A}
            → substEq (_ ; ∅ ⊢_) eqB₁ (L · substEq (_ ; ∅ ⊢_) (sym eqA₁) L')
              ≡ substEq (_ ; ∅ ⊢_) eq⇒₁ L · L'
          leftEq {L'} =
            trans
              (app-substEq eqA₁ eqB₁)
              (cong (λ e → substEq (_ ; ∅ ⊢_) e L · L') eq⇒-arr₁)

          rightEq : ∀ {M' : Ξ ; ∅ ⊢ substᵗ (λ α → τ₂ (ρ α)) A}
            → substEq (_ ; ∅ ⊢_) eqB₂ (M · substEq (_ ; ∅ ⊢_) (sym eqA₂) M')
              ≡ substEq (_ ; ∅ ⊢_) eq⇒₂ M · M'
          rightEq {M'} =
            trans
              (app-substEq eqA₂ eqB₂)
              (cong (λ e → substEq (_ ; ∅ ⊢_) e M · M') eq⇒-arr₂)

          body : ∀ {L' : Ξ ; ∅ ⊢ substᵗ (λ α → τ₁ (ρ α)) A}
                   {M' : Ξ ; ∅ ⊢ substᵗ (λ α → τ₂ (ρ α)) A}
            → ValueRel n A (renameTySubstRel ρ τ₁~τ₂) L' M'
            → TermRel n B (renameTySubstRel ρ τ₁~τ₂)
                (substEq (_ ; ∅ ⊢_) eq⇒₁ L · L')
                (substEq (_ ; ∅ ⊢_) eq⇒₂ M · M')
          body {L'} {M'} N~ =
            transport-TermRel n B (renameTySubstRel ρ τ₁~τ₂) leftEq rightEq
              (renameᵗ-TermRel↓ n ρ B τ₁~τ₂
                (VW~ (renameᵗ-ValueRel↑ n ρ A τ₁~τ₂ N~)))
  renameᵗ-ValueRel↓ zero ρ {τ₁ = τ₁} {τ₂ = τ₂} (∀̇ A) τ₁~τ₂ VW = go VW
    where
      go : ∀ {L M} → ValueRel zero (renameᵗ ρ (∀̇ A)) τ₁~τ₂ L M
        → ValueRel zero (∀̇ A) (renameTySubstRel ρ τ₁~τ₂)
            (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₁ (∀̇ A)) L)
            (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₂ (∀̇ A)) M)
      go ⟨ vV , ⟨ vW , u ⟩ ⟩ =
        ⟨ transport-Value (substᵗ-renameᵗ ρ τ₁ (∀̇ A)) vV
        , ⟨ transport-Value (substᵗ-renameᵗ ρ τ₂ (∀̇ A)) vW
          , u ⟩ ⟩
  renameᵗ-ValueRel↓ (suc n) {Ξ = Ξ} ρ {τ₁ = τ₁} {τ₂ = τ₂} (∀̇ A) τ₁~τ₂ {L} {M}
    ⟨ vL , ⟨ vM , LM~ ⟩ ⟩ =
      ⟨ transport-Value (substᵗ-renameᵗ ρ τ₁ (∀̇ A)) vL
      , ⟨ transport-Value (substᵗ-renameᵗ ρ τ₂ (∀̇ A)) vM
        , body ⟩ ⟩
    where
    body : ∀ {A₁ A₂ : Type Ξ}
      → (A₁~A₂ : TyRel A₁ A₂)
      → TermRel n A (extTySubstRel (renameTySubstRel ρ τ₁~τ₂) A₁~A₂)
          (inst∀ A (λ α → τ₁ (ρ α)) A₁
            (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₁ (∀̇ A)) L))
          (inst∀ A (λ α → τ₂ (ρ α)) A₂
            (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₂ (∀̇ A)) M))
    body {A₁} {A₂} A₁~A₂ =
      TermRel-congTySubst n A
        eq₁ eq₂ ρ→ρ' ρ'→ρ
        (renameᵗ-inst∀↓ ρ τ₁ A A₁)
        (renameᵗ-inst∀↓ ρ τ₂ A A₂)
        (renameᵗ-TermRel↓ n (extᵗ ρ) A (extTySubstRel τ₁~τ₂ A₁~A₂) (LM~ A₁~A₂))
      where
      eq₁ : ∀ α → (τ₁ ,ᵗ A₁) (extᵗ ρ α) ≡ ((λ β → τ₁ (ρ β)) ,ᵗ A₁) α
      eq₁ α = sym (rename-ext-point ρ τ₁ A₁ α)

      eq₂ : ∀ α → (τ₂ ,ᵗ A₂) (extᵗ ρ α) ≡ ((λ β → τ₂ (ρ β)) ,ᵗ A₂) α
      eq₂ α = sym (rename-ext-point ρ τ₂ A₂ α)

      ρ→ρ' : ∀ α {V W}
        → renameTySubstRel (extᵗ ρ) (extTySubstRel τ₁~τ₂ A₁~A₂) α V W
        → extTySubstRel (renameTySubstRel ρ τ₁~τ₂) A₁~A₂ α
            (substEq (_ ; ∅ ⊢_) (eq₁ α) V)
            (substEq (_ ; ∅ ⊢_) (eq₂ α) W)
      ρ→ρ' Z VW = VW
      ρ→ρ' (S α) VW = VW

      ρ'→ρ : ∀ α {V W}
        → extTySubstRel (renameTySubstRel ρ τ₁~τ₂) A₁~A₂ α V W
        → renameTySubstRel (extᵗ ρ) (extTySubstRel τ₁~τ₂ A₁~A₂) α
            (substEq (_ ; ∅ ⊢_) (sym (eq₁ α)) V)
            (substEq (_ ; ∅ ⊢_) (sym (eq₂ α)) W)
      ρ'→ρ Z VW = VW
      ρ'→ρ (S α) VW = VW

  renameᵗ-TermRel↑ : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} (ρ : Δ₁ ⇒ʳ Δ₂) {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
    → (A : Type Δ₁)
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → {L : Ξ ; ∅ ⊢ substᵗ (λ α → τ₁ (ρ α)) A}
    → {M : Ξ ; ∅ ⊢ substᵗ (λ α → τ₂ (ρ α)) A}
    → TermRel n A (renameTySubstRel ρ τ₁~τ₂) L M
    → TermRel n (renameᵗ ρ A) τ₁~τ₂
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₁ A)) L)
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₂ A)) M)
  renameᵗ-TermRel↑ n ρ {τ₁ = τ₁} {τ₂ = τ₂} A τ₁~τ₂
    ⟨ V , ⟨ W , ⟨ L—↠V , ⟨ M—↠W , VW ⟩ ⟩ ⟩ ⟩ =
      ⟨ substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₁ A)) V
      , ⟨ substEq (_ ; ∅ ⊢_) (sym (substᵗ-renameᵗ ρ τ₂ A)) W
        , ⟨ transport-↠ (sym (substᵗ-renameᵗ ρ τ₁ A)) L—↠V
          , ⟨ transport-↠ (sym (substᵗ-renameᵗ ρ τ₂ A)) M—↠W
            , renameᵗ-ValueRel↑ n ρ A τ₁~τ₂ VW
            ⟩ ⟩ ⟩ ⟩

  renameᵗ-TermRel↓ : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} (ρ : Δ₁ ⇒ʳ Δ₂) {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
    → (A : Type Δ₁)
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → {L : Ξ ; ∅ ⊢ substᵗ τ₁ (renameᵗ ρ A)}
    → {M : Ξ ; ∅ ⊢ substᵗ τ₂ (renameᵗ ρ A)}
    → TermRel n (renameᵗ ρ A) τ₁~τ₂ L M
    → TermRel n A (renameTySubstRel ρ τ₁~τ₂)
        (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₁ A) L)
        (substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₂ A) M)
  renameᵗ-TermRel↓ n ρ {τ₁ = τ₁} {τ₂ = τ₂} A τ₁~τ₂
    ⟨ V , ⟨ W , ⟨ L—↠V , ⟨ M—↠W , VW ⟩ ⟩ ⟩ ⟩ =
      ⟨ substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₁ A) V
      , ⟨ substEq (_ ; ∅ ⊢_) (substᵗ-renameᵗ ρ τ₂ A) W
        , ⟨ transport-↠ (substᵗ-renameᵗ ρ τ₁ A) L—↠V
          , ⟨ transport-↠ (substᵗ-renameᵗ ρ τ₂ A) M—↠W
            , renameᵗ-ValueRel↓ n ρ A τ₁~τ₂ VW
            ⟩ ⟩ ⟩ ⟩

SubstRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
  → (Γ : Ctx Δ)
  → TySubstRel {ℓ} τ₁ τ₂
  → (substCtx τ₁ Γ) →ˢ ∅
  → (substCtx τ₂ Γ) →ˢ ∅
  → Set (lsuc (lsuc ℓ))
SubstRel n {τ₁ = τ₁} {τ₂} Γ τ₁~τ₂ σ₁ σ₂ =
  ∀ {A} (x : Γ ∋ A) →
    TermRel n A τ₁~τ₂ (σ₁ (substᵗ-∋ τ₁ x)) (σ₂ (substᵗ-∋ τ₂ x))

extSubst : ∀ {Ξ Δ} {τ : Δ ⇒ˢ Ξ} {Γ : Ctx Δ} {A : Type Δ}
  → (substCtx τ Γ →ˢ ∅)
  → Ξ ; ∅ ⊢ substᵗ τ A
  → substCtx τ (Γ , A) →ˢ ∅
extSubst {A = A} σ V Z      = V
extSubst {A = A} σ V (S x)  = σ x

exts-cong : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  {σ σ' : Γ →ˢ Γ'}
  → (∀ {B} (x : Γ ∋ B) → σ x ≡ σ' x)
  → ∀ {B} (x : Γ , A ∋ B) → exts σ x ≡ exts σ' x
exts-cong eq Z = refl
exts-cong eq (S x) = cong ⇑ (eq x)

⇑ˢ-cong : ∀ {Δ} {Γ Γ' : Ctx Δ}
  {σ σ' : Γ →ˢ Γ'}
  → (∀ {A} (x : Γ ∋ A) → σ x ≡ σ' x)
  → ∀ {A} (x : ⇑ᶜ Γ ∋ A) → ⇑ˢ σ x ≡ ⇑ˢ σ' x
⇑ˢ-cong {Γ = ∅} eq ()
⇑ˢ-cong {Γ = Γ , A} eq Z = cong ⇑ᵀ (eq Z)
⇑ˢ-cong {Γ = Γ , A} eq (S x) = ⇑ˢ-cong (λ y → eq (S y)) x

subst-cong : ∀ {Δ} {Γ Γ' : Ctx Δ} {A : Type Δ}
  {σ σ' : Γ →ˢ Γ'}
  → (M : Δ ; Γ ⊢ A)
  → (∀ {B} (x : Γ ∋ B) → σ x ≡ σ' x)
  → subst σ M ≡ subst σ' M
subst-cong `zero eq = refl
subst-cong (` x) eq = eq x
subst-cong (ƛ A ˙ N) eq = cong (ƛ A ˙_) (subst-cong N (exts-cong eq))
subst-cong (L · M) eq = cong₂ _·_ (subst-cong L eq) (subst-cong M eq)
subst-cong (Λ N) eq = cong Λ_ (subst-cong N (⇑ˢ-cong eq))
subst-cong (M ∙ B) eq = cong (_∙ B) (subst-cong M eq)

postulate
  substᵀ-ext : ∀ {Ξ Δ Γ A B}
    → (τ : Δ ⇒ˢ Ξ)
    → (σ : substCtx τ Γ →ˢ ∅)
    → (V : Ξ ; ∅ ⊢ substᵗ τ A)
    → (N : Δ ; Γ , A ⊢ B)
    → subst (σ₀ V) (subst (exts σ) (substᵀ τ N))
      ≡ subst (extSubst {A = A} σ V) (substᵀ τ N)

  substᵀ-Λ-ext : ∀ {Ξ Δ Γ A} (τ : Δ ⇒ˢ Ξ) (B : Type Ξ)
    → (σ : substCtx τ Γ →ˢ ∅)
    → (N : Δ ,α ; ⇑ᶜ Γ ⊢ A)
    → let σ↑ = substEq (λ Γ' → Γ' →ˢ ∅) (sym (substCtx-,ᵗ-⇑ᶜ-cancel τ B Γ)) σ
      in inst∀ A τ B (subst σ (substᵀ τ (Λ N)))
         —↠ subst σ↑ (substᵀ (τ ,ᵗ B) N)

extSubRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ} {Γ : Ctx Δ} {A : Type Δ}
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → {σ₁ : substCtx τ₁ Γ →ˢ ∅}
    → {σ₂ : substCtx τ₂ Γ →ˢ ∅}
    → SubstRel n Γ τ₁~τ₂ σ₁ σ₂
    → {V : Ξ ; ∅ ⊢ substᵗ τ₁ A}
    → {W : Ξ ; ∅ ⊢ substᵗ τ₂ A}
    → ValueRel n A τ₁~τ₂ V W
    → SubstRel n (Γ , A) τ₁~τ₂ (extSubst {A = A} σ₁ V) (extSubst {A = A} σ₂ W)
extSubRel n τ₁~τ₂ σ₁~σ₂ VW Z = ValueRel⇒TermRel n _ τ₁~τ₂ VW
extSubRel n τ₁~τ₂ σ₁~σ₂ VW (S x) = σ₁~σ₂ x



postulate
  liftSubstRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ} {Γ : Ctx Δ}
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → {σ₁ : substCtx τ₁ Γ →ˢ ∅}
    → {σ₂ : substCtx τ₂ Γ →ˢ ∅}
    → SubstRel n Γ τ₁~τ₂ σ₁ σ₂
    → SubstRel (suc n) Γ τ₁~τ₂ σ₁ σ₂

  downSubstRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ} {Γ : Ctx Δ}
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → {σ₁ : substCtx τ₁ Γ →ˢ ∅}
    → {σ₂ : substCtx τ₂ Γ →ˢ ∅}
    → SubstRel (suc n) Γ τ₁~τ₂ σ₁ σ₂
    → SubstRel n Γ τ₁~τ₂ σ₁ σ₂

inst∀-start : ∀ {Ξ Δ Γ} {τ : Δ ⇒ˢ Ξ}
  → (A : Type (Δ ,α))
  → (B : Type Δ)
  → (M : Δ ; Γ ⊢ ∀̇ A)
  → (σ : substCtx τ Γ →ˢ ∅)
  → subst σ (substᵀ τ (M ∙ B)) —↠
      substEq (_ ; ∅ ⊢_) (sym (subst-[] A τ B))
        (inst∀ A τ (substᵗ τ B) (subst σ (substᵀ τ M)))
inst∀-start {τ = τ} A B M σ
  rewrite substᵗ-[]ᵗ τ A B
        | ∀-[] A τ (substᵗ τ B) = _ ∎


substTyRel→TermRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
    → (A : Type Δ)
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → ∀ {L M} → substTyRel A τ₁~τ₂ L M → TermRel n A τ₁~τ₂ L M
substTyRel→TermRel n A rel (lift lower) = {!!}

postulate
  ValueRel→substTyRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
    → (A : Type Δ)
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → ∀ {L M} → ValueRel n A τ₁~τ₂ L M → substTyRel A τ₁~τ₂ L M

SubstTySubstRel : ∀ {ℓ Ξ Δ₁ Δ₂} {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
  → (σ : Δ₁ ⇒ˢ Δ₂)
  → Set (lsuc (lsuc ℓ))
SubstTySubstRel {τ₁ = τ₁} {τ₂} σ =
  TySubstRel (λ α → substᵗ τ₁ (σ α)) (λ α → substᵗ τ₂ (σ α))

substᵗ-ValueRel↑-var : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
  → (σ : Δ₁ ⇒ˢ Δ₂)
  → (α : TyVar Δ₁)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
  → (σ~V : ∀ (k : Nat) β {L M}
      → Value L
      → Value M
      → σ~ β L M
      → ValueRel k (σ β) τ₁~τ₂ L M)
  → (σ~↓ : ∀ (k : Nat) β {L M}
      → ValueRel k (σ β) τ₁~τ₂ L M
      → σ~ β L M)
  → {L : Ξ ; ∅ ⊢ substᵗ (λ β → substᵗ τ₁ (σ β)) (` α)}
  → {M : Ξ ; ∅ ⊢ substᵗ (λ β → substᵗ τ₂ (σ β)) (` α)}
  → ValueRel n (` α) σ~ L M
  → ValueRel n (substᵗ σ (` α)) τ₁~τ₂
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ (` α))) L)
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ (` α))) M)
substᵗ-ValueRel↑-var n {τ₁ = τ₁} {τ₂ = τ₂} σ α τ₁~τ₂ σ~ σ~V σ~↓ ⟨ vL , ⟨ vM , lift LM~ ⟩ ⟩
  rewrite substᵗ-comp σ τ₁ (` α) | substᵗ-comp σ τ₂ (` α) =
    σ~V n α vL vM LM~

substᵗ-ValueRel↓-var : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
  → (σ : Δ₁ ⇒ˢ Δ₂)
  → (α : TyVar Δ₁)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
  → (σ~V : ∀ (k : Nat) β {L M}
      → Value L
      → Value M
      → σ~ β L M
      → ValueRel k (σ β) τ₁~τ₂ L M)
  → (σ~↓ : ∀ (k : Nat) β {L M}
      → ValueRel k (σ β) τ₁~τ₂ L M
      → σ~ β L M)
  → {L : Ξ ; ∅ ⊢ substᵗ (λ β → substᵗ τ₁ (σ β)) (` α)}
  → {M : Ξ ; ∅ ⊢ substᵗ (λ β → substᵗ τ₂ (σ β)) (` α)}
  → ValueRel n (substᵗ σ (` α)) τ₁~τ₂
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ (` α))) L)
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ (` α))) M)
  → ValueRel n (` α) σ~ L M
substᵗ-ValueRel↓-var n {τ₁ = τ₁} {τ₂ = τ₂} σ α τ₁~τ₂ σ~ σ~V σ~↓ LM
  rewrite substᵗ-comp σ τ₁ (` α) | substᵗ-comp σ τ₂ (` α) =
    ⟨ ValueRel-left n (σ α) τ₁~τ₂ LM
    , ⟨ ValueRel-right n (σ α) τ₁~τ₂ LM
      , lift (σ~↓ n α LM) ⟩ ⟩

substᵗ-ValueRel↑-Nat : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
  → (σ : Δ₁ ⇒ˢ Δ₂)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
  → (σ~V : ∀ (k : Nat) α {L M}
      → Value L
      → Value M
      → σ~ α L M
      → ValueRel k (σ α) τ₁~τ₂ L M)
  → (σ~↓ : ∀ (k : Nat) α {L M}
      → ValueRel k (σ α) τ₁~τ₂ L M
      → σ~ α L M)
  → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) `Nat}
  → {M : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) `Nat}
  → ValueRel n `Nat σ~ L M
  → ValueRel n (substᵗ σ `Nat) τ₁~τ₂
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ `Nat)) L)
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ `Nat)) M)
substᵗ-ValueRel↑-Nat n {τ₁ = τ₁} {τ₂ = τ₂} σ τ₁~τ₂ σ~ σ~V σ~↓ LM
  rewrite substᵗ-comp σ τ₁ `Nat | substᵗ-comp σ τ₂ `Nat = LM

substᵗ-ValueRel↓-Nat : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
  → (σ : Δ₁ ⇒ˢ Δ₂)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
  → (σ~V : ∀ (k : Nat) α {L M}
      → Value L
      → Value M
      → σ~ α L M
      → ValueRel k (σ α) τ₁~τ₂ L M)
  → (σ~↓ : ∀ (k : Nat) α {L M}
      → ValueRel k (σ α) τ₁~τ₂ L M
      → σ~ α L M)
  → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) `Nat}
  → {M : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) `Nat}
  → ValueRel n (substᵗ σ `Nat) τ₁~τ₂
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ `Nat)) L)
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ `Nat)) M)
  → ValueRel n `Nat σ~ L M
substᵗ-ValueRel↓-Nat n {τ₁ = τ₁} {τ₂ = τ₂} σ τ₁~τ₂ σ~ σ~V σ~↓ LM
  rewrite substᵗ-comp σ τ₁ `Nat | substᵗ-comp σ τ₂ `Nat = LM

substᵗ-ValueRel↑-∀zero : ∀ {ℓ Ξ Δ₁ Δ₂} {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
  → (σ : Δ₁ ⇒ˢ Δ₂)
  → (A : Type (Δ₁ ,α))
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
  → (σ~V : ∀ (k : Nat) α {L M}
      → Value L
      → Value M
      → σ~ α L M
      → ValueRel k (σ α) τ₁~τ₂ L M)
  → (σ~↓ : ∀ (k : Nat) α {L M}
      → ValueRel k (σ α) τ₁~τ₂ L M
      → σ~ α L M)
  → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) (∀̇ A)}
  → {M : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) (∀̇ A)}
  → ValueRel zero (∀̇ A) σ~ L M
  → ValueRel zero (substᵗ σ (∀̇ A)) τ₁~τ₂
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ (∀̇ A))) L)
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ (∀̇ A))) M)
substᵗ-ValueRel↑-∀zero {τ₁ = τ₁} {τ₂ = τ₂} σ A τ₁~τ₂ σ~ σ~V σ~↓ ⟨ vL , ⟨ vM , u ⟩ ⟩ =
  ⟨ transport-Value (sym (substᵗ-comp σ τ₁ (∀̇ A))) vL
  , ⟨ transport-Value (sym (substᵗ-comp σ τ₂ (∀̇ A))) vM
    , u ⟩ ⟩

substᵗ-ValueRel↓-∀zero : ∀ {ℓ Ξ Δ₁ Δ₂} {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
  → (σ : Δ₁ ⇒ˢ Δ₂)
  → (A : Type (Δ₁ ,α))
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
  → (σ~V : ∀ (k : Nat) α {L M}
      → Value L
      → Value M
      → σ~ α L M
      → ValueRel k (σ α) τ₁~τ₂ L M)
  → (σ~↓ : ∀ (k : Nat) α {L M}
      → ValueRel k (σ α) τ₁~τ₂ L M
      → σ~ α L M)
  → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) (∀̇ A)}
  → {M : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) (∀̇ A)}
  → ValueRel zero (substᵗ σ (∀̇ A)) τ₁~τ₂
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ (∀̇ A))) L)
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ (∀̇ A))) M)
  → ValueRel zero (∀̇ A) σ~ L M
substᵗ-ValueRel↓-∀zero {τ₁ = τ₁} {τ₂ = τ₂} σ A τ₁~τ₂ σ~ σ~V σ~↓ {L = L} {M = M} LM =
  transport-ValueRel zero (∀̇ A) σ~
    (substEq-sym-cancel {P = _ ; ∅ ⊢_} (substᵗ-comp σ τ₁ (∀̇ A)))
    (substEq-sym-cancel {P = _ ; ∅ ⊢_} (substᵗ-comp σ τ₂ (∀̇ A)))
    mid
  where
  mid : ValueRel zero (∀̇ A) σ~
      (substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₁ (∀̇ A))
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ (∀̇ A))) L))
      (substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₂ (∀̇ A))
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ (∀̇ A))) M))
  mid =
    ⟨ transport-Value (substᵗ-comp σ τ₁ (∀̇ A))
        (ValueRel-left zero (substᵗ σ (∀̇ A)) τ₁~τ₂ LM)
    , ⟨ transport-Value (substᵗ-comp σ τ₂ (∀̇ A))
          (ValueRel-right zero (substᵗ σ (∀̇ A)) τ₁~τ₂ LM)
      , lift tt ⟩ ⟩

mutual
  substᵗ-ValueRel↑ : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} (σ : Δ₁ ⇒ˢ Δ₂) {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
    → (A : Type Δ₁)
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
    → (σ~V : ∀ (k : Nat) α {L M} → Value L → Value M → σ~ α L M → ValueRel k (σ α) τ₁~τ₂ L M)
    → (σ~↓ : ∀ (k : Nat) α {L M} → ValueRel k (σ α) τ₁~τ₂ L M → σ~ α L M)
    → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) A}
    → {M : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) A}
    → ValueRel n A σ~ L M
    → ValueRel n (substᵗ σ A) τ₁~τ₂
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ A)) L)
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ A)) M)

  substᵗ-ValueRel↓ : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} (σ : Δ₁ ⇒ˢ Δ₂) {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
    → (A : Type Δ₁)
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
    → (σ~V : ∀ (k : Nat) α {L M} → Value L → Value M → σ~ α L M → ValueRel k (σ α) τ₁~τ₂ L M)
    → (σ~↓ : ∀ (k : Nat) α {L M} → ValueRel k (σ α) τ₁~τ₂ L M → σ~ α L M)
    → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) A}
    → {M : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) A}
    → ValueRel n (substᵗ σ A) τ₁~τ₂
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ A)) L)
      (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ A)) M)
    → ValueRel n A σ~ L M

  substᵗ-TermRel↑ : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} (σ : Δ₁ ⇒ˢ Δ₂) {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
    → (A : Type Δ₁)
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
    → (σ~V : ∀ (k : Nat) α {L M} → Value L → Value M → σ~ α L M → ValueRel k (σ α) τ₁~τ₂ L M)
    → (σ~↓ : ∀ (k : Nat) α {L M} → ValueRel k (σ α) τ₁~τ₂ L M → σ~ α L M)
    → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) A}
    → {M : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) A}
    → TermRel n A σ~ L M
    → TermRel n (substᵗ σ A) τ₁~τ₂
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ A)) L)
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ A)) M)

  substᵗ-TermRel↓ : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} (σ : Δ₁ ⇒ˢ Δ₂) {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
    → (A : Type Δ₁)
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
    → (σ~V : ∀ (k : Nat) α {L M} → Value L → Value M → σ~ α L M → ValueRel k (σ α) τ₁~τ₂ L M)
    → (σ~↓ : ∀ (k : Nat) α {L M} → ValueRel k (σ α) τ₁~τ₂ L M → σ~ α L M)
    → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) A}
    → {M : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) A}
    → TermRel n (substᵗ σ A) τ₁~τ₂
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ A)) L)
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ A)) M)
    → TermRel n A σ~ L M

  substᵗ-∀-body↑ : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
    → (σ : Δ₁ ⇒ˢ Δ₂)
    → (A : Type (Δ₁ ,α))
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
    → (σ~V : ∀ (k : Nat) α {L M}
        → Value L
        → Value M
        → σ~ α L M
        → ValueRel k (σ α) τ₁~τ₂ L M)
    → (σ~↓ : ∀ (k : Nat) α {L M}
        → ValueRel k (σ α) τ₁~τ₂ L M
        → σ~ α L M)
    → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) (∀̇ A)}
    → {M : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) (∀̇ A)}
    → {A₁ A₂ : Type Ξ}
    → (A₁~A₂ : TyRel {ℓ} A₁ A₂)
    → TermRel n A (extTySubstRel σ~ A₁~A₂)
        (inst∀ A (λ α → substᵗ τ₁ (σ α)) A₁ L)
        (inst∀ A (λ α → substᵗ τ₂ (σ α)) A₂ M)
    → TermRel n (substᵗ (extsᵗ σ) A) (extTySubstRel τ₁~τ₂ A₁~A₂)
        (inst∀ (substᵗ (extsᵗ σ) A) τ₁ A₁
          (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ (∀̇ A))) L))
        (inst∀ (substᵗ (extsᵗ σ) A) τ₂ A₂
          (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ (∀̇ A))) M))

  substᵗ-∀-body↓ : ∀ (n : Nat) {ℓ Ξ Δ₁ Δ₂} {τ₁ τ₂ : Δ₂ ⇒ˢ Ξ}
    → (σ : Δ₁ ⇒ˢ Δ₂)
    → (A : Type (Δ₁ ,α))
    → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → (σ~ : SubstTySubstRel {ℓ} {Ξ} {τ₁ = τ₁} {τ₂} σ)
    → (σ~V : ∀ (k : Nat) α {L M}
        → Value L
        → Value M
        → σ~ α L M
        → ValueRel k (σ α) τ₁~τ₂ L M)
    → (σ~↓ : ∀ (k : Nat) α {L M}
        → ValueRel k (σ α) τ₁~τ₂ L M
        → σ~ α L M)
    → {L : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) (∀̇ A)}
    → {M : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) (∀̇ A)}
    → {A₁ A₂ : Type Ξ}
    → (A₁~A₂ : TyRel {ℓ} A₁ A₂)
    → TermRel n (substᵗ (extsᵗ σ) A) (extTySubstRel τ₁~τ₂ A₁~A₂)
        (inst∀ (substᵗ (extsᵗ σ) A) τ₁ A₁
          (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ (∀̇ A))) L))
        (inst∀ (substᵗ (extsᵗ σ) A) τ₂ A₂
          (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ (∀̇ A))) M))
    → TermRel n A (extTySubstRel σ~ A₁~A₂)
        (inst∀ A (λ α → substᵗ τ₁ (σ α)) A₁ L)
        (inst∀ A (λ α → substᵗ τ₂ (σ α)) A₂ M)

  substᵗ-ValueRel↑ n σ (` α) τ₁~τ₂ σ~ σ~V σ~↓ =
    substᵗ-ValueRel↑-var n σ α τ₁~τ₂ σ~ σ~V σ~↓
  substᵗ-ValueRel↑ n σ `Nat τ₁~τ₂ σ~ σ~V σ~↓ =
    substᵗ-ValueRel↑-Nat n σ τ₁~τ₂ σ~ σ~V σ~↓
  substᵗ-ValueRel↑ n {Ξ = Ξ} σ {τ₁ = τ₁} {τ₂ = τ₂} (A ⇒ B) τ₁~τ₂ σ~ σ~V σ~↓ {L = F} {M = G}
    ⟨ vF , ⟨ vG , FG~ ⟩ ⟩ =
      ⟨ transport-Value (sym compArr₁) vF
      , ⟨ transport-Value (sym compArr₂) vG
        , body ⟩ ⟩
    where
    compA₁ = substᵗ-comp σ τ₁ A
    compA₂ = substᵗ-comp σ τ₂ A
    compB₁ = substᵗ-comp σ τ₁ B
    compB₂ = substᵗ-comp σ τ₂ B
    compArr₁ = substᵗ-comp σ τ₁ (A ⇒ B)
    compArr₂ = substᵗ-comp σ τ₂ (A ⇒ B)

    eqArr₁ : cong₂ _⇒_ (sym compA₁) (sym compB₁) ≡ sym compArr₁
    eqArr₁ = Type-≡-irrelevant _ _

    eqArr₂ : cong₂ _⇒_ (sym compA₂) (sym compB₂) ≡ sym compArr₂
    eqArr₂ = Type-≡-irrelevant _ _

    arg↓ : ∀ {L′ : Ξ ; ∅ ⊢ substᵗ τ₁ (substᵗ σ A)}
             {M′ : Ξ ; ∅ ⊢ substᵗ τ₂ (substᵗ σ A)}
      → ValueRel n (substᵗ σ A) τ₁~τ₂ L′ M′
      → ValueRel n A σ~
          (substEq (_ ; ∅ ⊢_) compA₁ L′)
          (substEq (_ ; ∅ ⊢_) compA₂ M′)
    arg↓ {L′} {M′} N~ =
      substᵗ-ValueRel↓ n σ A τ₁~τ₂ σ~ σ~V σ~↓
        (transport-ValueRel n (substᵗ σ A) τ₁~τ₂
          (sym (substEq-cancel {P = _ ; ∅ ⊢_} compA₁))
          (sym (substEq-cancel {P = _ ; ∅ ⊢_} compA₂))
          N~)

    leftEq : ∀ {L′ : Ξ ; ∅ ⊢ substᵗ τ₁ (substᵗ σ A)}
      → substEq (_ ; ∅ ⊢_) (sym compB₁) (F · substEq (_ ; ∅ ⊢_) compA₁ L′)
        ≡ substEq (_ ; ∅ ⊢_) (sym compArr₁) F · L′
    leftEq {L′} =
      trans
        (sym (cong
          (λ e → substEq (_ ; ∅ ⊢_) (sym compB₁) (F · substEq (_ ; ∅ ⊢_) e L′))
          (sym-sym compA₁)))
        (trans
          (app-substEq (sym compA₁) (sym compB₁))
          (cong (λ e → substEq (_ ; ∅ ⊢_) e F · L′) eqArr₁))

    rightEq : ∀ {M′ : Ξ ; ∅ ⊢ substᵗ τ₂ (substᵗ σ A)}
      → substEq (_ ; ∅ ⊢_) (sym compB₂) (G · substEq (_ ; ∅ ⊢_) compA₂ M′)
        ≡ substEq (_ ; ∅ ⊢_) (sym compArr₂) G · M′
    rightEq {M′} =
      trans
        (sym (cong
          (λ e → substEq (_ ; ∅ ⊢_) (sym compB₂) (G · substEq (_ ; ∅ ⊢_) e M′))
          (sym-sym compA₂)))
        (trans
          (app-substEq (sym compA₂) (sym compB₂))
          (cong (λ e → substEq (_ ; ∅ ⊢_) e G · M′) eqArr₂))

    body : ∀ {L′ : Ξ ; ∅ ⊢ substᵗ τ₁ (substᵗ σ A)}
             {M′ : Ξ ; ∅ ⊢ substᵗ τ₂ (substᵗ σ A)}
      → ValueRel n (substᵗ σ A) τ₁~τ₂ L′ M′
      → TermRel n (substᵗ σ B) τ₁~τ₂
          (substEq (_ ; ∅ ⊢_) (sym compArr₁) F · L′)
          (substEq (_ ; ∅ ⊢_) (sym compArr₂) G · M′)
    body {L′} {M′} N~ =
      transport-TermRel n (substᵗ σ B) τ₁~τ₂ leftEq rightEq
        (substᵗ-TermRel↑ n σ B τ₁~τ₂ σ~ σ~V σ~↓
          (FG~ (arg↓ N~)))
  substᵗ-ValueRel↑ zero σ (∀̇ A) τ₁~τ₂ σ~ σ~V σ~↓ =
    substᵗ-ValueRel↑-∀zero σ A τ₁~τ₂ σ~ σ~V σ~↓
  substᵗ-ValueRel↑ (suc n) {Ξ = Ξ} σ {τ₁ = τ₁} {τ₂ = τ₂} (∀̇ A) τ₁~τ₂ σ~ σ~V σ~↓ {L = L} {M = M}
    ⟨ vL , ⟨ vM , LM~ ⟩ ⟩ =
      ⟨ transport-Value (sym (substᵗ-comp σ τ₁ (∀̇ A))) vL
      , ⟨ transport-Value (sym (substᵗ-comp σ τ₂ (∀̇ A))) vM
        , (λ A₁~A₂ → substᵗ-∀-body↑ n σ A τ₁~τ₂ σ~ σ~V σ~↓ A₁~A₂ (LM~ A₁~A₂)) ⟩ ⟩

  substᵗ-ValueRel↓ n σ (` α) τ₁~τ₂ σ~ σ~V σ~↓ =
    substᵗ-ValueRel↓-var n σ α τ₁~τ₂ σ~ σ~V σ~↓
  substᵗ-ValueRel↓ n σ `Nat τ₁~τ₂ σ~ σ~V σ~↓ =
    substᵗ-ValueRel↓-Nat n σ τ₁~τ₂ σ~ σ~V σ~↓
  substᵗ-ValueRel↓ n {Ξ = Ξ} σ {τ₁ = τ₁} {τ₂ = τ₂} (A ⇒ B) τ₁~τ₂ σ~ σ~V σ~↓ {L = F} {M = G}
    ⟨ vF , ⟨ vG , FG~ ⟩ ⟩ =
      ⟨ leftV , ⟨ rightV , body ⟩ ⟩
    where
    compA₁ = substᵗ-comp σ τ₁ A
    compA₂ = substᵗ-comp σ τ₂ A
    compB₁ = substᵗ-comp σ τ₁ B
    compB₂ = substᵗ-comp σ τ₂ B
    compArr₁ = substᵗ-comp σ τ₁ (A ⇒ B)
    compArr₂ = substᵗ-comp σ τ₂ (A ⇒ B)

    eqArr₁ : cong₂ _⇒_ (sym compA₁) (sym compB₁) ≡ sym compArr₁
    eqArr₁ = Type-≡-irrelevant _ _

    eqArr₂ : cong₂ _⇒_ (sym compA₂) (sym compB₂) ≡ sym compArr₂
    eqArr₂ = Type-≡-irrelevant _ _

    leftV : Value F
    leftV =
      substEq Value
        (substEq-sym-cancel {P = _ ; ∅ ⊢_} compArr₁)
        (transport-Value compArr₁ vF)

    rightV : Value G
    rightV =
      substEq Value
        (substEq-sym-cancel {P = _ ; ∅ ⊢_} compArr₂)
        (transport-Value compArr₂ vG)

    leftEq : ∀ {L′ : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) A}
      → substEq (_ ; ∅ ⊢_) (sym compB₁) (F · L′)
        ≡ substEq (_ ; ∅ ⊢_) (sym compArr₁) F
            · substEq (_ ; ∅ ⊢_) (sym compA₁) L′
    leftEq {L′} =
      trans
        (cong
          (λ x → substEq (_ ; ∅ ⊢_) (sym compB₁) (F · x))
          (sym (substEq-sym-cancel {P = _ ; ∅ ⊢_} compA₁)))
        (trans
          (sym (cong
            (λ e →
              substEq (_ ; ∅ ⊢_) (sym compB₁)
                (F · substEq (_ ; ∅ ⊢_) e
                  (substEq (_ ; ∅ ⊢_) (sym compA₁) L′)))
            (sym-sym compA₁)))
          (trans
            (app-substEq (sym compA₁) (sym compB₁))
            (cong
              (λ e → substEq (_ ; ∅ ⊢_) e F
                  · substEq (_ ; ∅ ⊢_) (sym compA₁) L′)
              eqArr₁)))

    rightEq : ∀ {M′ : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) A}
      → substEq (_ ; ∅ ⊢_) (sym compB₂) (G · M′)
        ≡ substEq (_ ; ∅ ⊢_) (sym compArr₂) G
            · substEq (_ ; ∅ ⊢_) (sym compA₂) M′
    rightEq {M′} =
      trans
        (cong
          (λ x → substEq (_ ; ∅ ⊢_) (sym compB₂) (G · x))
          (sym (substEq-sym-cancel {P = _ ; ∅ ⊢_} compA₂)))
        (trans
          (sym (cong
            (λ e →
              substEq (_ ; ∅ ⊢_) (sym compB₂)
                (G · substEq (_ ; ∅ ⊢_) e
                  (substEq (_ ; ∅ ⊢_) (sym compA₂) M′)))
            (sym-sym compA₂)))
          (trans
            (app-substEq (sym compA₂) (sym compB₂))
            (cong
              (λ e → substEq (_ ; ∅ ⊢_) e G
                  · substEq (_ ; ∅ ⊢_) (sym compA₂) M′)
              eqArr₂)))

    body : ∀ {L′ : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₁ (σ α)) A}
             {M′ : Ξ ; ∅ ⊢ substᵗ (λ α → substᵗ τ₂ (σ α)) A}
      → ValueRel n A σ~ L′ M′
      → TermRel n B σ~ (F · L′) (G · M′)
    body {L′} {M′} N~ =
      substᵗ-TermRel↓ n σ B τ₁~τ₂ σ~ σ~V σ~↓
        (transport-TermRel n (substᵗ σ B) τ₁~τ₂
          (sym leftEq)
          (sym rightEq)
          (FG~ (substᵗ-ValueRel↑ n σ A τ₁~τ₂ σ~ σ~V σ~↓ N~)))
  substᵗ-ValueRel↓ zero σ (∀̇ A) τ₁~τ₂ σ~ σ~V σ~↓ =
    substᵗ-ValueRel↓-∀zero σ A τ₁~τ₂ σ~ σ~V σ~↓
  substᵗ-ValueRel↓ (suc n) {Ξ = Ξ} σ {τ₁ = τ₁} {τ₂ = τ₂} (∀̇ A) τ₁~τ₂ σ~ σ~V σ~↓ {L = L} {M = M}
    ⟨ vL , ⟨ vM , LM~ ⟩ ⟩ =
      ⟨ substEq Value
          (substEq-sym-cancel {P = _ ; ∅ ⊢_} (substᵗ-comp σ τ₁ (∀̇ A)))
          (transport-Value (substᵗ-comp σ τ₁ (∀̇ A)) vL)
      , ⟨ substEq Value
            (substEq-sym-cancel {P = _ ; ∅ ⊢_} (substᵗ-comp σ τ₂ (∀̇ A)))
            (transport-Value (substᵗ-comp σ τ₂ (∀̇ A)) vM)
        , (λ A₁~A₂ → substᵗ-∀-body↓ n σ A τ₁~τ₂ σ~ σ~V σ~↓ A₁~A₂ (LM~ A₁~A₂)) ⟩ ⟩

  substᵗ-TermRel↑ n σ {τ₁ = τ₁} {τ₂} A τ₁~τ₂ σ~ σ~V σ~↓
    ⟨ V , ⟨ W , ⟨ L—↠V , ⟨ M—↠W , VW ⟩ ⟩ ⟩ ⟩ =
      ⟨ substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ A)) V
      , ⟨ substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ A)) W
        , ⟨ transport-↠ (sym (substᵗ-comp σ τ₁ A)) L—↠V
          , ⟨ transport-↠ (sym (substᵗ-comp σ τ₂ A)) M—↠W
            , substᵗ-ValueRel↑ n σ A τ₁~τ₂ σ~ σ~V σ~↓ VW
            ⟩ ⟩ ⟩ ⟩

  substᵗ-TermRel↓ n σ {τ₁ = τ₁} {τ₂ = τ₂} A τ₁~τ₂ σ~ σ~V σ~↓ {L = L} {M = M} LM =
    transport-TermRel n A σ~
      (substEq-sym-cancel (substᵗ-comp σ τ₁ A))
      (substEq-sym-cancel (substᵗ-comp σ τ₂ A))
      mid
    where
    go : TermRel n (substᵗ σ A) τ₁~τ₂
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ A)) L)
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ A)) M)
      → TermRel n A σ~
          (substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₁ A)
            (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ A)) L))
          (substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₂ A)
            (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ A)) M))
    go ⟨ V , ⟨ W , ⟨ L—↠V , ⟨ M—↠W , VW ⟩ ⟩ ⟩ ⟩ =
      ⟨ substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₁ A) V
      , ⟨ substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₂ A) W
        , ⟨ transport-↠ (substᵗ-comp σ τ₁ A) L—↠V
          , ⟨ transport-↠ (substᵗ-comp σ τ₂ A) M—↠W
            , substᵗ-ValueRel↓ n σ A τ₁~τ₂ σ~ σ~V σ~↓
                {L = substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₁ A) V}
                {M = substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₂ A) W}
                VW′
            ⟩ ⟩ ⟩ ⟩
      where
      VW′ : ValueRel n (substᵗ σ A) τ₁~τ₂
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ A))
          (substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₁ A) V))
        (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ A))
          (substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₂ A) W))
      VW′ = transport-ValueRel n (substᵗ σ A) τ₁~τ₂
        (sym (substEq-cancel (substᵗ-comp σ τ₁ A)))
        (sym (substEq-cancel (substᵗ-comp σ τ₂ A)))
        VW

    mid : TermRel n A σ~
        (substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₁ A)
          (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₁ A)) L))
        (substEq (_ ; ∅ ⊢_) (substᵗ-comp σ τ₂ A)
          (substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp σ τ₂ A)) M))
    mid = go LM

  substᵗ-∀-body↑ n {τ₁ = τ₁} {τ₂ = τ₂} σ A τ₁~τ₂ σ~ σ~V σ~↓
    {L = L} {M = M} {A₁ = A₁} {A₂ = A₂} A₁~A₂ LM =
    transport-TermRel n (substᵗ (extsᵗ σ) A) (extTySubstRel τ₁~τ₂ A₁~A₂)
      (substᵗ-inst∀↑ σ τ₁ A A₁)
      (substᵗ-inst∀↑ σ τ₂ A A₂)
      (substᵗ-TermRel↑ n (extsᵗ σ) A (extTySubstRel τ₁~τ₂ A₁~A₂) σ↑~ σ↑~V σ↑~↓
        (TermRel-congTySubst n A eq₁ eq₂ ρ→σ↑ σ↑→ρ refl refl LM))
    where
    eq₁ : ∀ α
      → ((λ β → substᵗ τ₁ (σ β)) ,ᵗ A₁) α ≡ substᵗ (τ₁ ,ᵗ A₁) (extsᵗ σ α)
    eq₁ = subst-ext-point σ τ₁ A₁
  
    eq₂ : ∀ α
      → ((λ β → substᵗ τ₂ (σ β)) ,ᵗ A₂) α ≡ substᵗ (τ₂ ,ᵗ A₂) (extsᵗ σ α)
    eq₂ = subst-ext-point σ τ₂ A₂
  
    σ↑~ : TySubstRel
      (λ α → substᵗ (τ₁ ,ᵗ A₁) (extsᵗ σ α))
      (λ α → substᵗ (τ₂ ,ᵗ A₂) (extsᵗ σ α))
    σ↑~ Z V W = A₁~A₂ V W
    σ↑~ (S α) V W =
      σ~ α
        (substEq (_ ; ∅ ⊢_) (sym (eq₁ (S α))) V)
        (substEq (_ ; ∅ ⊢_) (sym (eq₂ (S α))) W)
  
    ρ→σ↑ : ∀ α {V W}
      → extTySubstRel σ~ A₁~A₂ α V W
      → σ↑~ α
          (substEq (_ ; ∅ ⊢_) (eq₁ α) V)
          (substEq (_ ; ∅ ⊢_) (eq₂ α) W)
    ρ→σ↑ Z VW = VW
    ρ→σ↑ (S α) {V} {W} VW =
      substEq
        (λ Y →
          σ~ α
            (substEq (_ ; ∅ ⊢_) (sym (eq₁ (S α)))
              (substEq (_ ; ∅ ⊢_) (eq₁ (S α)) V))
            Y)
        (sym (substEq-cancel {P = _ ; ∅ ⊢_} (eq₂ (S α)) {u = W}))
        (substEq
          (λ X → σ~ α X W)
          (sym (substEq-cancel {P = _ ; ∅ ⊢_} (eq₁ (S α)) {u = V}))
          VW)
  
    σ↑→ρ : ∀ α {V W}
      → σ↑~ α V W
      → extTySubstRel σ~ A₁~A₂ α
          (substEq (_ ; ∅ ⊢_) (sym (eq₁ α)) V)
          (substEq (_ ; ∅ ⊢_) (sym (eq₂ α)) W)
    σ↑→ρ Z VW = VW
    σ↑→ρ (S α) VW = VW
  
    σ↑~V : ∀ (k : Nat) α {V W}
      → Value V
      → Value W
      → σ↑~ α V W
      → ValueRel k (extsᵗ σ α) (extTySubstRel τ₁~τ₂ A₁~A₂) V W
    σ↑~V k Z vV vW VW = ⟨ vV , ⟨ vW , lift VW ⟩ ⟩
    σ↑~V k (S α) {V} {W} vV vW VW =
      transport-ValueRel k (extsᵗ σ (S α)) (extTySubstRel τ₁~τ₂ A₁~A₂)
        (substEq-cancel {P = _ ; ∅ ⊢_} renameEq₁)
        (substEq-cancel {P = _ ; ∅ ⊢_} renameEq₂)
        (renameᵗ-ValueRel↑ k S_ (σ α) (extTySubstRel τ₁~τ₂ A₁~A₂)
          (σ~V k α
            (transport-Value renameEq₁ vV)
            (transport-Value renameEq₂ vW)
            rel))
      where
      renameEq₁ = substᵗ-renameᵗ S_ (τ₁ ,ᵗ A₁) (σ α)
      renameEq₂ = substᵗ-renameᵗ S_ (τ₂ ,ᵗ A₂) (σ α)
  
      rel : σ~ α
        (substEq (_ ; ∅ ⊢_) renameEq₁ V)
        (substEq (_ ; ∅ ⊢_) renameEq₂ W)
      rel =
        substEq
          (λ p₂ → σ~ α (substEq (_ ; ∅ ⊢_) renameEq₁ V) (substEq (_ ; ∅ ⊢_) p₂ W))
          (Type-≡-irrelevant (sym (eq₂ (S α))) renameEq₂)
          (substEq
            (λ p₁ → σ~ α (substEq (_ ; ∅ ⊢_) p₁ V) (substEq (_ ; ∅ ⊢_) (sym (eq₂ (S α))) W))
            (Type-≡-irrelevant (sym (eq₁ (S α))) renameEq₁)
            VW)
  
    σ↑~↓ : ∀ (k : Nat) α {V W}
      → ValueRel k (extsᵗ σ α) (extTySubstRel τ₁~τ₂ A₁~A₂) V W
      → σ↑~ α V W
    σ↑~↓ k Z ⟨ _ , ⟨ _ , lift VW ⟩ ⟩ = VW
    σ↑~↓ k (S α) {V} {W} VW = rel
      where
      renameEq₁ = substᵗ-renameᵗ S_ (τ₁ ,ᵗ A₁) (σ α)
      renameEq₂ = substᵗ-renameᵗ S_ (τ₂ ,ᵗ A₂) (σ α)
  
      rel' : σ~ α
        (substEq (_ ; ∅ ⊢_) renameEq₁ V)
        (substEq (_ ; ∅ ⊢_) renameEq₂ W)
      rel' = σ~↓ k α (renameᵗ-ValueRel↓ k S_ (σ α) (extTySubstRel τ₁~τ₂ A₁~A₂) VW)
  
      rel : σ↑~ (S α) V W
      rel =
        substEq
          (λ p₂ → σ~ α (substEq (_ ; ∅ ⊢_) (sym (eq₁ (S α))) V) (substEq (_ ; ∅ ⊢_) p₂ W))
          (Type-≡-irrelevant renameEq₂ (sym (eq₂ (S α))))
          (substEq
            (λ p₁ → σ~ α (substEq (_ ; ∅ ⊢_) p₁ V) (substEq (_ ; ∅ ⊢_) renameEq₂ W))
            (Type-≡-irrelevant renameEq₁ (sym (eq₁ (S α))))
            rel')
  
  substᵗ-∀-body↓ n {τ₁ = τ₁} {τ₂ = τ₂} σ A τ₁~τ₂ σ~ σ~V σ~↓
    {L = L} {M = M} {A₁ = A₁} {A₂ = A₂} A₁~A₂ LM =
    TermRel-congTySubst n A
      (λ α → sym (eq₁ α))
      (λ α → sym (eq₂ α))
      σ↑→ρ
      ρ→σ↑'
      (sym (substᵗ-cong-sym-cancel A eq₁))
      (sym (substᵗ-cong-sym-cancel A eq₂))
      (substᵗ-TermRel↓ n (extsᵗ σ) A (extTySubstRel τ₁~τ₂ A₁~A₂) σ↑~ σ↑~V σ↑~↓
        (transport-TermRel n (substᵗ (extsᵗ σ) A) (extTySubstRel τ₁~τ₂ A₁~A₂)
          (sym (substᵗ-inst∀↑ σ τ₁ A A₁))
          (sym (substᵗ-inst∀↑ σ τ₂ A A₂))
          LM))
    where
    eq₁ : ∀ α
      → ((λ β → substᵗ τ₁ (σ β)) ,ᵗ A₁) α ≡ substᵗ (τ₁ ,ᵗ A₁) (extsᵗ σ α)
    eq₁ = subst-ext-point σ τ₁ A₁
  
    eq₂ : ∀ α
      → ((λ β → substᵗ τ₂ (σ β)) ,ᵗ A₂) α ≡ substᵗ (τ₂ ,ᵗ A₂) (extsᵗ σ α)
    eq₂ = subst-ext-point σ τ₂ A₂
  
    σ↑~ : TySubstRel
      (λ α → substᵗ (τ₁ ,ᵗ A₁) (extsᵗ σ α))
      (λ α → substᵗ (τ₂ ,ᵗ A₂) (extsᵗ σ α))
    σ↑~ Z V W = A₁~A₂ V W
    σ↑~ (S α) V W =
      σ~ α
        (substEq (_ ; ∅ ⊢_) (sym (eq₁ (S α))) V)
        (substEq (_ ; ∅ ⊢_) (sym (eq₂ (S α))) W)
  
    σ↑→ρ : ∀ α {V W}
      → σ↑~ α V W
      → extTySubstRel σ~ A₁~A₂ α
          (substEq (_ ; ∅ ⊢_) (sym (eq₁ α)) V)
          (substEq (_ ; ∅ ⊢_) (sym (eq₂ α)) W)
    σ↑→ρ Z VW = VW
    σ↑→ρ (S α) VW = VW
  
    ρ→σ↑' : ∀ α {V W}
      → extTySubstRel σ~ A₁~A₂ α V W
      → σ↑~ α
          (substEq (_ ; ∅ ⊢_) (sym (sym (eq₁ α))) V)
          (substEq (_ ; ∅ ⊢_) (sym (sym (eq₂ α))) W)
    ρ→σ↑' Z VW = VW
    ρ→σ↑' (S α) {V} {W} VW
      rewrite sym-sym (eq₁ (S α))
            | sym-sym (eq₂ (S α))
      = ρ→σ↑ (S α) VW
      where
      ρ→σ↑ : ∀ β {X Y}
        → extTySubstRel σ~ A₁~A₂ β X Y
        → σ↑~ β
            (substEq (_ ; ∅ ⊢_) (eq₁ β) X)
            (substEq (_ ; ∅ ⊢_) (eq₂ β) Y)
      ρ→σ↑ Z UV = UV
      ρ→σ↑ (S β) {X} {Y} UV =
        substEq
          (λ Y' →
            σ~ β
              (substEq (_ ; ∅ ⊢_) (sym (eq₁ (S β)))
                (substEq (_ ; ∅ ⊢_) (eq₁ (S β)) X))
              Y')
          (sym (substEq-cancel {P = _ ; ∅ ⊢_} (eq₂ (S β)) {u = Y}))
          (substEq
            (λ X' → σ~ β X' Y)
            (sym (substEq-cancel {P = _ ; ∅ ⊢_} (eq₁ (S β)) {u = X}))
            UV)
  
    σ↑~V : ∀ (k : Nat) α {V W}
      → Value V
      → Value W
      → σ↑~ α V W
      → ValueRel k (extsᵗ σ α) (extTySubstRel τ₁~τ₂ A₁~A₂) V W
    σ↑~V k Z vV vW VW = ⟨ vV , ⟨ vW , lift VW ⟩ ⟩
    σ↑~V k (S α) {V} {W} vV vW VW =
      transport-ValueRel k (extsᵗ σ (S α)) (extTySubstRel τ₁~τ₂ A₁~A₂)
        (substEq-cancel {P = _ ; ∅ ⊢_} renameEq₁)
        (substEq-cancel {P = _ ; ∅ ⊢_} renameEq₂)
        (renameᵗ-ValueRel↑ k S_ (σ α) (extTySubstRel τ₁~τ₂ A₁~A₂)
          (σ~V k α
            (transport-Value renameEq₁ vV)
            (transport-Value renameEq₂ vW)
            rel))
      where
      renameEq₁ = substᵗ-renameᵗ S_ (τ₁ ,ᵗ A₁) (σ α)
      renameEq₂ = substᵗ-renameᵗ S_ (τ₂ ,ᵗ A₂) (σ α)
  
      rel : σ~ α
        (substEq (_ ; ∅ ⊢_) renameEq₁ V)
        (substEq (_ ; ∅ ⊢_) renameEq₂ W)
      rel =
        substEq
          (λ p₂ → σ~ α (substEq (_ ; ∅ ⊢_) renameEq₁ V) (substEq (_ ; ∅ ⊢_) p₂ W))
          (Type-≡-irrelevant (sym (eq₂ (S α))) renameEq₂)
          (substEq
            (λ p₁ → σ~ α (substEq (_ ; ∅ ⊢_) p₁ V) (substEq (_ ; ∅ ⊢_) (sym (eq₂ (S α))) W))
            (Type-≡-irrelevant (sym (eq₁ (S α))) renameEq₁)
            VW)
  
    σ↑~↓ : ∀ (k : Nat) α {V W}
      → ValueRel k (extsᵗ σ α) (extTySubstRel τ₁~τ₂ A₁~A₂) V W
      → σ↑~ α V W
    σ↑~↓ k Z ⟨ _ , ⟨ _ , lift VW ⟩ ⟩ = VW
    σ↑~↓ k (S α) {V} {W} VW = rel
      where
      renameEq₁ = substᵗ-renameᵗ S_ (τ₁ ,ᵗ A₁) (σ α)
      renameEq₂ = substᵗ-renameᵗ S_ (τ₂ ,ᵗ A₂) (σ α)
  
      rel' : σ~ α
        (substEq (_ ; ∅ ⊢_) renameEq₁ V)
        (substEq (_ ; ∅ ⊢_) renameEq₂ W)
      rel' = σ~↓ k α (renameᵗ-ValueRel↓ k S_ (σ α) (extTySubstRel τ₁~τ₂ A₁~A₂) VW)
  
      rel : σ↑~ (S α) V W
      rel =
        substEq
          (λ p₂ → σ~ α (substEq (_ ; ∅ ⊢_) (sym (eq₁ (S α))) V) (substEq (_ ; ∅ ⊢_) p₂ W))
          (Type-≡-irrelevant renameEq₂ (sym (eq₂ (S α))))
          (substEq
            (λ p₁ → σ~ α (substEq (_ ; ∅ ⊢_) p₁ V) (substEq (_ ; ∅ ⊢_) renameEq₂ W))
            (Type-≡-irrelevant renameEq₁ (sym (eq₁ (S α))))
            rel')
  
[]-TermRel↑ : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
  → (A : Type (Δ ,α))
  → (B : Type Δ)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → (B~ : TyRel {ℓ} (substᵗ τ₁ B) (substᵗ τ₂ B))
  → (B~↑ : ∀ (k : Nat) {L M} → B~ L M → TermRel k B τ₁~τ₂ L M)
  → (B~↓ : ∀ (k : Nat) {L M} → ValueRel k B τ₁~τ₂ L M → B~ L M)
  → {L : Ξ ; ∅ ⊢ substᵗ (τ₁ ,ᵗ substᵗ τ₁ B) A}
  → {M : Ξ ; ∅ ⊢ substᵗ (τ₂ ,ᵗ substᵗ τ₂ B) A}
  → TermRel n A (extTySubstRel τ₁~τ₂ B~) L M
  → TermRel n (A [ B ]ᵗ) τ₁~τ₂
      (substEq (_ ; ∅ ⊢_) (sym (subst-[] A τ₁ B)) L)
      (substEq (_ ; ∅ ⊢_) (sym (subst-[] A τ₂ B)) M)
[]-TermRel↑ n {τ₁ = τ₁} {τ₂ = τ₂} A B τ₁~τ₂ B~ B~↑ B~↓ {L} {M} LM =
  transport-TermRel n (A [ B ]ᵗ) τ₁~τ₂ left right
    (substᵗ-TermRel↑ n (σ₀ᵗ B) A τ₁~τ₂ σ₀~ σ₀~V σ₀~↓ LM′)
  where
  eq₁ : ∀ α → (τ₁ ,ᵗ substᵗ τ₁ B) α ≡ substᵗ τ₁ (σ₀ᵗ B α)
  eq₁ = σ₀ᵗ-point τ₁ B

  eq₂ : ∀ α → (τ₂ ,ᵗ substᵗ τ₂ B) α ≡ substᵗ τ₂ (σ₀ᵗ B α)
  eq₂ = σ₀ᵗ-point τ₂ B

  σ₀~ : TySubstRel
    (λ α → substᵗ τ₁ (σ₀ᵗ B α))
    (λ α → substᵗ τ₂ (σ₀ᵗ B α))
  σ₀~ Z      = B~
  σ₀~ (S α)  = τ₁~τ₂ α

  ρ→σ₀ : ∀ α {V W}
    → extTySubstRel τ₁~τ₂ B~ α V W
    → σ₀~ α (substEq (_ ; ∅ ⊢_) (eq₁ α) V) (substEq (_ ; ∅ ⊢_) (eq₂ α) W)
  ρ→σ₀ Z VW = VW
  ρ→σ₀ (S α) VW = VW

  σ₀→ρ : ∀ α {V W}
    → σ₀~ α V W
    → extTySubstRel τ₁~τ₂ B~ α
        (substEq (_ ; ∅ ⊢_) (sym (eq₁ α)) V)
        (substEq (_ ; ∅ ⊢_) (sym (eq₂ α)) W)
  σ₀→ρ Z VW = VW
  σ₀→ρ (S α) VW = VW

  LM′ : TermRel n A σ₀~
      (substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₁) L)
      (substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₂) M)
  LM′ = TermRel-congTySubst n A eq₁ eq₂ ρ→σ₀ σ₀→ρ refl refl LM

  σ₀~V : ∀ (k : Nat) α {V W}
    → Value V
    → Value W
    → σ₀~ α V W
    → ValueRel k (σ₀ᵗ B α) τ₁~τ₂ V W
  σ₀~V k Z vV vW VW = TermRel→ValueRel k B τ₁~τ₂ vV vW {!LM!}
  σ₀~V k (S α) vV vW VW = ⟨ vV , ⟨ vW , lift VW ⟩ ⟩

  σ₀~↓ : ∀ (k : Nat) α {V W}
    → ValueRel k (σ₀ᵗ B α) τ₁~τ₂ V W
    → σ₀~ α V W
  σ₀~↓ k Z VW = B~↓ k VW
  σ₀~↓ k (S α) ⟨ _ , ⟨ _ , lift VW ⟩ ⟩ = VW

  left : substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp (σ₀ᵗ B) τ₁ A))
            (substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₁) L)
       ≡ substEq (_ ; ∅ ⊢_) (sym (subst-[] A τ₁ B)) L
  left = trans
    (substEq-trans (substᵗ-cong A eq₁) (sym (substᵗ-comp (σ₀ᵗ B) τ₁ A)) L)
    (cong (λ e → substEq (_ ; ∅ ⊢_) e L) (σ₀ᵗ-comp-[] A τ₁ B))

  right : substEq (_ ; ∅ ⊢_) (sym (substᵗ-comp (σ₀ᵗ B) τ₂ A))
             (substEq (_ ; ∅ ⊢_) (substᵗ-cong A eq₂) M)
        ≡ substEq (_ ; ∅ ⊢_) (sym (subst-[] A τ₂ B)) M
  right = trans
    (substEq-trans (substᵗ-cong A eq₂) (sym (substᵗ-comp (σ₀ᵗ B) τ₂ A)) M)
    (cong (λ e → substEq (_ ; ∅ ⊢_) e M) (σ₀ᵗ-comp-[] A τ₂ B))

∀-elim-TermRel : ∀ (n : Nat) {ℓ Ξ Δ Γ} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
  → (A : Type (Δ ,α))
  → (B : Type Δ)
  → (M : Δ ; Γ ⊢ ∀̇ A)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → (σ₁ : substCtx τ₁ Γ →ˢ ∅)
  → (σ₂ : substCtx τ₂ Γ →ˢ ∅)
  → TermRel (suc n) (∀̇ A) τ₁~τ₂ (subst σ₁ (substᵀ τ₁ M)) (subst σ₂ (substᵀ τ₂ M))
  → TermRel n (A [ B ]ᵗ) τ₁~τ₂
      (subst σ₁ (substᵀ τ₁ (M ∙ B)))
      (subst σ₂ (substᵀ τ₂ (M ∙ B)))
∀-elim-TermRel n {τ₁ = τ₁} {τ₂} A B M τ₁~τ₂ σ₁ σ₂
  ⟨ V , ⟨ W , ⟨ M—↠V , ⟨ M′—↠W , ⟨ _ , ⟨ _ , frel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  TermRel-anti-reduction n (A [ B ]ᵗ) τ₁~τ₂
    (—↠-trans
      (inst∀-start {τ = τ₁} A B M σ₁)
      (transport-↠ (sym (subst-[] A τ₁ B))
        (transport-↠ (∀-[] A τ₁ (substᵗ τ₁ B))
          (∙-↠ {B = substᵗ τ₁ B} M—↠V))))
    (—↠-trans
      (inst∀-start {τ = τ₂} A B M σ₂)
      (transport-↠ (sym (subst-[] A τ₂ B))
        (transport-↠ (∀-[] A τ₂ (substᵗ τ₂ B))
          (∙-↠ {B = substᵗ τ₂ B} M′—↠W))))
    ([]-TermRel↑ n A B τ₁~τ₂
      (substTyRel B τ₁~τ₂)
      -- (λ k → substTyRel→TermRel k B τ₁~τ₂)
      {!!}
      (λ k → ValueRel→substTyRel k B τ₁~τ₂)
      (frel (substTyRel B τ₁~τ₂)))

shiftSubstRel : ∀ (n : Nat) {ℓ Ξ Δ} {τ₁ τ₂ : Δ ⇒ˢ Ξ} {Γ : Ctx Δ}
      → {σ₁ : substCtx τ₁ Γ →ˢ ∅}
      → {σ₂ : substCtx τ₂ Γ →ˢ ∅}
      → {A₁ A₂ : Type Ξ}
      → {σ₁↑ : substCtx (τ₁ ,ᵗ A₁) (⇑ᶜ Γ) →ˢ ∅}
      → {σ₂↑ : substCtx (τ₂ ,ᵗ A₂) (⇑ᶜ Γ) →ˢ ∅}
      → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
      → SubstRel n Γ τ₁~τ₂ σ₁ σ₂
      → (A₁~A₂ : TyRel {ℓ} A₁ A₂)
        ------------------------------------------------------------------------------------
      → SubstRel n (⇑ᶜ Γ) (extTySubstRel τ₁~τ₂ A₁~A₂) σ₁↑ σ₂↑
shiftSubstRel n rel srel trel x = {!!}

fundamental :
  ∀ (n : Nat) {ℓ Ξ Δ Γ A} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
  → (M : Δ ; Γ ⊢ A)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
  → (σ₁ : (substCtx τ₁ Γ) →ˢ ∅)
  → (σ₂ : (substCtx τ₂ Γ) →ˢ ∅)
  → SubstRel n Γ τ₁~τ₂ σ₁ σ₂
    ------------------------------------------------------------------------------
  → TermRel n A τ₁~τ₂ (subst σ₁ (substᵀ τ₁ M)) (subst σ₂ (substᵀ τ₂ M))
fundamental n `zero τ₁~τ₂ σ₁ σ₂ σ₁~σ₂ =
  ValueRel⇒TermRel n `Nat τ₁~τ₂ ⟨ V-zero , ⟨ V-zero , lift refl ⟩ ⟩
fundamental n (` x) τ₁~τ₂ σ₁ σ₂ σ₁~σ₂ =
  σ₁~σ₂ x
fundamental n {A = A ⇒ B} {τ₁ = τ₁} {τ₂} (ƛ A ˙ N) τ₁~τ₂ σ₁ σ₂ σ₁~σ₂ =
  ValueRel⇒TermRel n (A ⇒ B) τ₁~τ₂
    ⟨ V-ƛ , ⟨ V-ƛ , body ⟩ ⟩
  where
  ih : ∀ {V W}
    → ValueRel n A τ₁~τ₂ V W
    → TermRel n B τ₁~τ₂
        (subst (extSubst {A = A} σ₁ V) (substᵀ τ₁ N))
        (subst (extSubst {A = A} σ₂ W) (substᵀ τ₂ N))
  ih {V} {W} V~W =
    fundamental n N τ₁~τ₂
      (extSubst {A = A} σ₁ V)
      (extSubst {A = A} σ₂ W)
      (extSubRel n τ₁~τ₂ σ₁~σ₂ V~W)
  body : ∀ {L M}
    → ValueRel n A τ₁~τ₂ L M
    → TermRel n B τ₁~τ₂
        (subst σ₁ (substᵀ τ₁ (ƛ A ˙ N)) · L)
        (subst σ₂ (substᵀ τ₂ (ƛ A ˙ N)) · M)
  body {L} {M} L~M =
    TermRel-anti-reduction n B τ₁~τ₂
      (step-eq-↠ (β-ƛ (ValueRel-left n A τ₁~τ₂ L~M))
        (substᵀ-ext τ₁ σ₁ L N))
      (step-eq-↠ (β-ƛ (ValueRel-right n A τ₁~τ₂ L~M))
        (substᵀ-ext τ₂ σ₂ M N))
      (ih L~M)
fundamental n {A = B} (L · M) τ₁~τ₂ σ₁ σ₂ σ₁~σ₂
  with fundamental n L τ₁~τ₂ σ₁ σ₂ σ₁~σ₂
     | fundamental n M τ₁~τ₂ σ₁ σ₂ σ₁~σ₂
... | ⟨ V₁ , ⟨ W₁ , ⟨ L—↠V₁ , ⟨ L′—↠W₁ , ⟨ vV₁ , ⟨ vW₁ , frel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ V₂ , ⟨ W₂ , ⟨ M—↠V₂ , ⟨ M′—↠W₂ , V₂~W₂ ⟩ ⟩ ⟩ ⟩ =
      TermRel-anti-reduction n B τ₁~τ₂
        (—↠-trans (·₁-↠ L—↠V₁) (·₂-↠ vV₁ M—↠V₂))
        (—↠-trans (·₁-↠ L′—↠W₁) (·₂-↠ vW₁ M′—↠W₂))
        (frel V₂~W₂)
fundamental zero {A = ∀̇ A} (Λ N) τ₁~τ₂ σ₁ σ₂ σ₁~σ₂ =
  ValueRel⇒TermRel zero (∀̇ A) τ₁~τ₂ ⟨ V-Λ , ⟨ V-Λ , lift tt ⟩ ⟩
fundamental (suc n) {ℓ = ℓ} {Ξ = Ξ} {Γ = Γ} {A = ∀̇ A} {τ₁ = τ₁} {τ₂} (Λ N) τ₁~τ₂ σ₁ σ₂ σ₁~σ₂ =
  ValueRel⇒TermRel (suc n) (∀̇ A) τ₁~τ₂
    ⟨ V-Λ , ⟨ V-Λ , ih ⟩ ⟩
  where
  ih : ∀ {A₁ A₂ : Type Ξ}
    → (A₁~A₂ : TyRel {ℓ} A₁ A₂)
    → TermRel n A (extTySubstRel τ₁~τ₂ A₁~A₂)
        (inst∀ A τ₁ A₁ (subst σ₁ (substᵀ τ₁ (Λ N))))
        (inst∀ A τ₂ A₂ (subst σ₂ (substᵀ τ₂ (Λ N))))
  ih {A₁} {A₂} A₁~A₂ =
    TermRel-anti-reduction n A (extTySubstRel τ₁~τ₂ A₁~A₂)
      (substᵀ-Λ-ext τ₁ A₁ σ₁ N)
      (substᵀ-Λ-ext τ₂ A₂ σ₂ N)
      (fundamental n N (extTySubstRel τ₁~τ₂ A₁~A₂) σ₁↑ σ₂↑ σ↑~₂)
    where
    σ₁↑ : substCtx (τ₁ ,ᵗ A₁) (⇑ᶜ Γ) →ˢ ∅
    σ₁↑ = substEq (λ Γ' → Γ' →ˢ ∅) (sym (substCtx-,ᵗ-⇑ᶜ-cancel τ₁ A₁ Γ)) σ₁

    σ₂↑ : substCtx (τ₂ ,ᵗ A₂) (⇑ᶜ Γ) →ˢ ∅
    σ₂↑ = substEq (λ Γ' → Γ' →ˢ ∅) (sym (substCtx-,ᵗ-⇑ᶜ-cancel τ₂ A₂ Γ)) σ₂

    σ↑~₂ : SubstRel n (⇑ᶜ Γ) (extTySubstRel τ₁~τ₂ A₁~A₂) σ₁↑ σ₂↑
    σ↑~₂ = shiftSubstRel n {σ₁ = σ₁}{σ₂}{σ₁↑ = σ₁↑}{σ₂↑} τ₁~τ₂ (downSubstRel n τ₁~τ₂ {σ₁ = σ₁} {σ₂ = σ₂} σ₁~σ₂) A₁~A₂
fundamental n (_∙_ {A = A} M B) τ₁~τ₂ σ₁ σ₂ σ₁~σ₂ =
  ∀-elim-TermRel n A B M τ₁~τ₂ σ₁ σ₂
    (fundamental (suc n) M τ₁~τ₂ σ₁ σ₂
      (liftSubstRel n τ₁~τ₂ {σ₁ = σ₁} {σ₂ = σ₂} σ₁~σ₂))

parametricity :
  ∀ (n : Nat) {ℓ Ξ Δ A} {τ₁ τ₂ : Δ ⇒ˢ Ξ}
  → (M : Δ ; ∅ ⊢ A)
  → (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    ---------------------------------------------------------------------------
  → TermRel n A τ₁~τ₂ (subst _ (substᵀ τ₁ M)) (subst _ (substᵀ τ₂ M))
parametricity n {τ₁ = τ₁} {τ₂} M τ₁~τ₂ =
  fundamental n M τ₁~τ₂ (emptySub τ₁) (emptySub τ₂) (emptySubstRel n τ₁ τ₂ τ₁~τ₂)
  where
  emptySub : ∀ {Ξ Δ} (τ : Δ ⇒ˢ Ξ) → substCtx τ ∅ →ˢ ∅
  emptySub _ ()
  emptySubstRel : ∀ (n : Nat) {ℓ Ξ Δ} (τ₁ τ₂ : Δ ⇒ˢ Ξ) (τ₁~τ₂ : TySubstRel {ℓ} τ₁ τ₂)
    → SubstRel n ∅ τ₁~τ₂ (emptySub τ₁) (emptySub τ₂)
  emptySubstRel n τ₁ τ₂ τ₁~τ₂ ()
