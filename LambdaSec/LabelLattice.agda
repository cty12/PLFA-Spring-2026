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

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ x → f x ≡ g x)
    → f ≡ g

cong₃ : ∀ {A B C D : Set} {x x′ : A} {y y′ : B} {z z′ : C}
  (f : A → B → C → D)
  → x ≡ x′ → y ≡ y′ → z ≡ z′
  → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl
