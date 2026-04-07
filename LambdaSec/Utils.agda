{-# OPTIONS --rewriting #-}

module LambdaSec.Utils where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ x → f x ≡ g x)
    → f ≡ g

cong₃ : ∀ {A B C D : Set} {x x′ : A} {y y′ : B} {z z′ : C}
  (f : A → B → C → D)
  → x ≡ x′ → y ≡ y′ → z ≡ z′
  → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl
