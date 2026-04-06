{-# OPTIONS --rewriting #-}

module LambdaSec.TwoPointLattice where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import LambdaSec.LabelLattice using (LabelLattice)

data SecLabel : Set where
  low high : SecLabel

_⊔_ : SecLabel → SecLabel → SecLabel
low  ⊔ ℓ    = ℓ
high ⊔ _    = high

_≟_ : (ℓ₁ ℓ₂ : SecLabel) → Dec (ℓ₁ ≡ ℓ₂)
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
