{-# OPTIONS --rewriting #-}

open import LambdaSec.LabelLattice using (LabelLattice)
open import LambdaSec.Utils using (cong₃)

module LambdaSec.Erasure (𝑳 : LabelLattice) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Function using (case_of_)

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import LambdaSec.LambdaSec 𝑳 public


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
      ---------------
    → ErasedTerm Γ

  $ᵉ_of_ : ∀ {Γ}
    → Bool
    → ℒ
      ---------------
    → ErasedTerm Γ

  ƛᵉ_of_ : ∀ {Γ A}
    → ErasedTerm (Γ , A)
    → ℒ
      ---------------
    → ErasedTerm Γ

  _`∧ᵉ_ : ∀ {Γ}
    → ErasedTerm Γ
    → ErasedTerm Γ
      ---------------
    → ErasedTerm Γ

  _`∨ᵉ_ : ∀ {Γ}
    → ErasedTerm Γ
    → ErasedTerm Γ
      ---------------
    → ErasedTerm Γ

  _·ᵉ_ : ∀ {Γ}
    → ErasedTerm Γ
    → ErasedTerm Γ
      ---------------
    → ErasedTerm Γ

  ifᵉ_then_else_ : ∀ {Γ}
    → ErasedTerm Γ
    → ErasedTerm Γ
    → ErasedTerm Γ
      ---------------
    → ErasedTerm Γ

eraseᵛ : ∀ {Γ T ℓ}
    → Γ ⊢ᵛ T of ℓ
    → (ζ : ℒ)
    → Dec (ℓ ⊑ ζ)
      ---------------
    → ErasedTerm Γ
erase : ∀ {Γ T ℓ}
    → Γ ⊢ᵉ T of ℓ
    → (ζ : ℒ)
    → Dec (ℓ ⊑ ζ)
      ---------------
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
Γ →ʳₑ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A
Γ →ˢₑ Δ = ∀ {A} → Γ ∋ A → ErasedTerm Δ

infixr 6 _•ʳₑ_
_•ʳₑ_ : ∀ {Γ Δ A} → Δ ∋ A → Γ →ʳₑ Δ → (Γ , A) →ʳₑ Δ
(x •ʳₑ ρ) Z     = x
(x •ʳₑ ρ) (S y) = ρ y

⇑ʳₑ : ∀ {Γ Δ A} → Γ →ʳₑ Δ → Γ →ʳₑ (Δ , A)
⇑ʳₑ ρ x = S (ρ x)

extₑ : ∀ {Γ Δ A} → Γ →ʳₑ Δ → (Γ , A) →ʳₑ (Δ , A)
extₑ ρ = ext ρ

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
renameₑ-cong {ρ = ρ} {τ} ρ=τ (ƛᵉ N of ℓ) = cong (ƛᵉ_of ℓ) (renameₑ-cong exts-eq N)
  where
  exts-eq : ∀ {A} (x : _ ∋ A) → extₑ ρ x ≡ extₑ τ x
  exts-eq Z     = refl
  exts-eq (S x) = cong S_ (ρ=τ x)
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
eraseˢ σ ζ {A = T of ℓ} x = erase (σ x) ζ (ℓ ⊑? ζ)

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
substₑ-cong {σ = σ} {τ} σ=τ (ƛᵉ N of ℓ) = cong (ƛᵉ_of ℓ) (substₑ-cong exts-eq N)
  where
  exts-eq : ∀ {A} (x : _ ∋ A) → extsₑ σ x ≡ extsₑ τ x
  exts-eq Z     = refl
  exts-eq (S x) = cong (renameₑ S_) (σ=τ x)
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
      ---------------------------------------------------------------------
    → eraseᵛ (renameᵛ ρ V) ζ (ℓ ⊑? ζ) ≡ renameₑ ρ (eraseᵛ V ζ (ℓ ⊑? ζ))
  erase-renameᵛ ρ ($ b of ℓ) ζ with ℓ ⊑? ζ
  ... | yes _ = refl
  ... | no _ = refl
  erase-renameᵛ {T = A ⇒ (B of ℓ′)} ρ (ƛ N of ℓ) ζ with ℓ ⊑? ζ
  ... | yes _ = cong (ƛᵉ_of ℓ) (erase-renameᵉ (ext ρ) N ζ)
  ... | no _ = refl

  erase-renameᵉ : ∀ {Γ Δ T ℓ} (ρ : Γ →ʳ Δ) (M : Γ ⊢ᵉ T of ℓ) (ζ : ℒ)
      ---------------------------------------------------------------------
    → erase (renameᵉ ρ M) ζ (ℓ ⊑? ζ) ≡ renameₑ ρ (erase M ζ (ℓ ⊑? ζ))
  erase-renameᵉ ρ (` x) ζ = refl
  erase-renameᵉ ρ (val V) ζ = erase-renameᵛ ρ V ζ
  erase-renameᵉ ρ (L · M) ζ = cong₂ _·ᵉ_ (erase-renameᵉ ρ L ζ) (erase-renameᵉ ρ M ζ)
  erase-renameᵉ ρ (if L then M else N) ζ =
    cong₃ ifᵉ_then_else_ (erase-renameᵉ ρ L ζ) (erase-renameᵉ ρ M ζ) (erase-renameᵉ ρ N ζ)
  erase-renameᵉ ρ (M `∧ N) ζ = cong₂ _`∧ᵉ_ (erase-renameᵉ ρ M ζ) (erase-renameᵉ ρ N ζ)
  erase-renameᵉ ρ (M `∨ N) ζ = cong₂ _`∨ᵉ_ (erase-renameᵉ ρ M ζ) (erase-renameᵉ ρ N ζ)
  erase-renameᵉ {ℓ = ℓ₂} ρ (sub {A = T₁ of ℓ₁} M A<:B) ζ with ℓ₂ ⊑? ζ
  ... | yes _ = erase-renameᵉ ρ M ζ
  ... | no _ = refl

eraseˢ-exts : ∀ {Γ Δ A B} (σ : Γ →ˢ Δ) (ζ : ℒ) (x : Γ , A ∋ B)
    ---------------------------------------------------------------
  → eraseˢ (exts σ) ζ x ≡ extsₑ (eraseˢ σ ζ) x
eraseˢ-exts {B = T of ℓ} σ ζ Z = refl
eraseˢ-exts {B = T of ℓ} σ ζ (S x) = erase-renameᵉ S_ (σ x) ζ

mutual

  erase-substᵛ : ∀ {Γ Δ T ℓ} (σ : Γ →ˢ Δ) (ζ : ℒ)
    → (V : Γ ⊢ᵛ T of ℓ)
      ------------------------------------------------------------------------------
    → eraseᵛ (substᵛ σ V) ζ (ℓ ⊑? ζ) ≡ substₑ (eraseˢ σ ζ) (eraseᵛ V ζ (ℓ ⊑? ζ))
  erase-substᵛ σ ζ ($ b of ℓ) with ℓ ⊑? ζ
  ... | yes _ = refl
  ... | no _ = refl
  erase-substᵛ {T = A ⇒ B of ℓ′} σ ζ (ƛ N of ℓ) with ℓ ⊑? ζ
  ... | yes _ = cong (ƛᵉ_of ℓ)
                     (trans (erase-substᵉ (exts σ) ζ N)
                            (substₑ-cong (eraseˢ-exts σ ζ) (erase N ζ (ℓ′ ⊑? ζ))))
  ... | no _ = refl

  erase-substᵉ : ∀ {Γ Δ T ℓ} (σ : Γ →ˢ Δ) (ζ : ℒ)
    → (M : Γ ⊢ᵉ T of ℓ)
      ---------------------------------------------------------------------------
    → erase (substᵉ σ M) ζ (ℓ ⊑? ζ) ≡ substₑ (eraseˢ σ ζ) (erase M ζ (ℓ ⊑? ζ))
  erase-substᵉ σ ζ (` x) = refl
  erase-substᵉ σ ζ (val V) = erase-substᵛ σ ζ V
  erase-substᵉ σ ζ (L · M) = cong₂ _·ᵉ_ (erase-substᵉ σ ζ L) (erase-substᵉ σ ζ M)
  erase-substᵉ σ ζ (if L then M else N) =
    cong₃ ifᵉ_then_else_ (erase-substᵉ σ ζ L) (erase-substᵉ σ ζ M) (erase-substᵉ σ ζ N)
  erase-substᵉ σ ζ (M `∧ N) = cong₂ _`∧ᵉ_ (erase-substᵉ σ ζ M) (erase-substᵉ σ ζ N)
  erase-substᵉ σ ζ (M `∨ N) = cong₂ _`∨ᵉ_ (erase-substᵉ σ ζ M) (erase-substᵉ σ ζ N)
  erase-substᵉ {ℓ = ℓ₂} σ ζ (sub {A = T₁ of ℓ₁} M A<:B) with ℓ₂ ⊑? ζ
  ... | yes _ = erase-substᵉ {ℓ = ℓ₁} σ ζ M
  ... | no _ = refl

eraseˢ-σ₀ : ∀ {A ℓ₁ B} (V : ∅ ⊢ᵛ A of ℓ₁) (ζ : ℒ) (x : ∅ , A of ℓ₁ ∋ B)
    ------------------------------------------------------------------------
  → eraseˢ ((val V) • id) ζ x ≡ (eraseᵛ V ζ (ℓ₁ ⊑? ζ) •ₑ idₑ) x
eraseˢ-σ₀ {ℓ₁ = ℓ₁} V ζ Z with ℓ₁ ⊑? ζ
... | yes _ = refl
... | no _ = refl

erase-[] : ∀ {A T ℓ₁ ℓ₂} {N : ∅ , A of ℓ₁ ⊢ᵉ T of ℓ₂} {V : ∅ ⊢ᵛ A of ℓ₁} {ζ}
    ------------------------------------------------------------------------------------
  → erase (N [ val V ]) ζ (ℓ₂ ⊑? ζ) ≡ erase N ζ (ℓ₂ ⊑? ζ) [ eraseᵛ V ζ (ℓ₁ ⊑? ζ) ]ₑ
erase-[] {ℓ₁ = ℓ₁} {ℓ₂} {N = N} {V = V} {ζ = ζ} =
  trans (erase-substᵉ ((val V) • id) ζ N)
        (substₑ-cong (eraseˢ-σ₀ V ζ) (erase N ζ (ℓ₂ ⊑? ζ)))
{-# REWRITE erase-[] #-}


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

eraseᵛ-hidden : ∀ {Γ T ℓ ζ} (V : Γ ⊢ᵛ T of ℓ)
    → (¬ℓ⊑ζ : ¬ (ℓ ⊑ ζ))
    → eraseᵛ V ζ (no ¬ℓ⊑ζ) ≡ ●
eraseᵛ-hidden {T = `𝔹} ($ b of ℓ) ¬ℓ⊑ζ = refl
eraseᵛ-hidden {T = A ⇒ (B of ℓ′)} (ƛ N of ℓ) ¬ℓ⊑ζ = refl
{-# REWRITE eraseᵛ-hidden #-}

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
  ... | no ¬vis with (ℓ₂ ⊔ ℓₗ) ⊑? ζ
  ...   | yes res = contradiction (⊑-trans ⊔-upper₂ res) ¬vis
  ...   | no _ =
    ⇓ₑ-if-●
      (subst (λ d → erase L ζ d ⇓ₑ eraseᵛ ($ true of ℓₗ) ζ d) eq
             (sim L⇓true))

  sim {ζ = ζ} {M = if L then M₁ else N₁} (⇓-if-else {ℓₗ = ℓₗ} {ℓ₂ = ℓ₂} {V = V} {L = L} {M = M₁} {N = N₁} L⇓false N⇓V)
    with ℓₗ ⊑? ζ in eq
  ... | yes vis = ⇓ₑ-if-else
                     (subst (λ d → erase L ζ d ⇓ₑ $ᵉ false of ℓₗ) eq
                            (sim-bool-visible L⇓false vis))
                     (sim N⇓V)
  ... | no ¬vis with (ℓ₂ ⊔ ℓₗ) ⊑? ζ
  ...   | yes res = contradiction (⊑-trans ⊔-upper₂ res) ¬vis
  ...   | no _ =
    ⇓ₑ-if-●
      (subst (λ d → erase L ζ d ⇓ₑ eraseᵛ ($ false of ℓₗ) ζ d) eq
             (sim L⇓false))

  sim {ζ = ζ} {M = L · M₁} (⇓-app {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₃} {W = W} {V = V} {N = N} {L = L} {M = M₁} L⇓ƛ M⇓W N[W]⇓V)
    with ℓ₃ ⊑? ζ in eq
  ... | yes vis =
    subst
      (λ □ → erase L ζ (yes vis) ·ᵉ erase M₁ ζ (_ ⊑? ζ) ⇓ₑ □)
      (sym (eraseᵛ-stamp-visible V ℓ₃ vis))
      (⇓ₑ-app (subst (λ d → erase L ζ d ⇓ₑ ƛᵉ (erase N ζ (_ ⊑? ζ)) of ℓ₃) eq
                       (sim-lam-visible L⇓ƛ vis))
               (sim M⇓W) (sim N[W]⇓V))
  ... | no ¬vis with (ℓ₂ ⊔ ℓ₃) ⊑? ζ
  ...   | yes res = contradiction (⊑-trans ⊔-upper₂ res) ¬vis
  ...   | no _ =
    ⇓ₑ-app-●
      (subst (λ d → erase L ζ d ⇓ₑ eraseᵛ (ƛ N of ℓ₃) ζ d) eq
             (sim L⇓ƛ))
      (sim M⇓W)

⇓ₑ-deterministic : ∀ {M V W}
  → M ⇓ₑ V
  → M ⇓ₑ W
    ---------
  → V ≡ W
⇓ₑ-deterministic (⇓ₑ-val _) (⇓ₑ-val _) = refl
⇓ₑ-deterministic (⇓ₑ-∧ L⇓V M⇓W) (⇓ₑ-∧ L⇓V′ M⇓W′)
  rewrite ⇓ₑ-deterministic L⇓V L⇓V′
        | ⇓ₑ-deterministic M⇓W M⇓W′ = refl
⇓ₑ-deterministic (⇓ₑ-∨ L⇓V M⇓W) (⇓ₑ-∨ L⇓V′ M⇓W′)
  rewrite ⇓ₑ-deterministic L⇓V L⇓V′
        | ⇓ₑ-deterministic M⇓W M⇓W′ = refl
⇓ₑ-deterministic (⇓ₑ-if-then L⇓true M⇓V) (⇓ₑ-if-then L⇓true′ M⇓V′)
  with ⇓ₑ-deterministic L⇓true L⇓true′
... | refl = ⇓ₑ-deterministic M⇓V M⇓V′
⇓ₑ-deterministic (⇓ₑ-if-then L⇓true _) (⇓ₑ-if-else L⇓false _)
  with ⇓ₑ-deterministic L⇓true L⇓false
... | ()
⇓ₑ-deterministic (⇓ₑ-if-then L⇓true _) (⇓ₑ-if-● L⇓●)
  with ⇓ₑ-deterministic L⇓true L⇓●
... | ()
⇓ₑ-deterministic (⇓ₑ-if-else L⇓false _) (⇓ₑ-if-then L⇓true _)
  with ⇓ₑ-deterministic L⇓false L⇓true
... | ()
⇓ₑ-deterministic (⇓ₑ-if-else L⇓false N⇓V) (⇓ₑ-if-else L⇓false′ N⇓V′)
  with ⇓ₑ-deterministic L⇓false L⇓false′
... | refl = ⇓ₑ-deterministic N⇓V N⇓V′
⇓ₑ-deterministic (⇓ₑ-if-else L⇓false _) (⇓ₑ-if-● L⇓●)
  with ⇓ₑ-deterministic L⇓false L⇓●
... | ()
⇓ₑ-deterministic (⇓ₑ-if-● L⇓●) (⇓ₑ-if-then L⇓true _)
  with ⇓ₑ-deterministic L⇓● L⇓true
... | ()
⇓ₑ-deterministic (⇓ₑ-if-● L⇓●) (⇓ₑ-if-else L⇓false _)
  with ⇓ₑ-deterministic L⇓● L⇓false
... | ()
⇓ₑ-deterministic (⇓ₑ-if-● _) (⇓ₑ-if-● _) = refl
⇓ₑ-deterministic (⇓ₑ-app L⇓ƛ M⇓V N[V]⇓W) (⇓ₑ-app L⇓ƛ′ M⇓V′ N[V]⇓W′)
  with ⇓ₑ-deterministic L⇓ƛ L⇓ƛ′
... | refl with ⇓ₑ-deterministic M⇓V M⇓V′
...   | refl with ⇓ₑ-deterministic N[V]⇓W N[V]⇓W′
...     | refl = refl
⇓ₑ-deterministic (⇓ₑ-app L⇓ƛ _ _) (⇓ₑ-app-● L⇓● _)
  with ⇓ₑ-deterministic L⇓ƛ L⇓●
... | ()
⇓ₑ-deterministic (⇓ₑ-app-● L⇓● _) (⇓ₑ-app L⇓ƛ _ _)
  with ⇓ₑ-deterministic L⇓● L⇓ƛ
... | ()
⇓ₑ-deterministic (⇓ₑ-app-● _ _) (⇓ₑ-app-● _ _) = refl
