{-# OPTIONS --rewriting #-}

module LambdaSec.LabelLattice where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec)

record LabelLattice : Set₁ where

  infixl 6 _⊔_

  field
    ℒ           : Set
    ⊥ₗ          : ℒ
    _⊔_         : ℒ → ℒ → ℒ
    _≟ₗ_        : ∀ (ℓ₁ ℓ₂ : ℒ) → Dec (ℓ₁ ≡ ℓ₂)
    ⊥ₗ-identity : ∀ {ℓ} → ⊥ₗ ⊔ ℓ ≡ ℓ
    ⊔-assoc     : ∀ {ℓ₁ ℓ₂ ℓ₃} → (ℓ₁ ⊔ ℓ₂) ⊔ ℓ₃ ≡ ℓ₁ ⊔ (ℓ₂ ⊔ ℓ₃)
    ⊔-comm      : ∀ {ℓ₁ ℓ₂} → ℓ₁ ⊔ ℓ₂ ≡ ℓ₂ ⊔ ℓ₁
    ⊔-idem      : ∀ {ℓ} → ℓ ⊔ ℓ ≡ ℓ
