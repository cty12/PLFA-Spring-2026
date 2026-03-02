module Renaming (Context : Set) (Type : Set) (_∋_ : Context → Type → Set) where


infixr 7 _→ʳ_
_→ʳ_ : Context → Context → Set
Γ →ʳ Δ = (∀ {A} → Γ ∋ A → Δ ∋ A)

infixr 6 _•ʳ_
_•ʳ_ : ∀{Γ Δ A} → (Δ ∋ A) → (Γ →ʳ Δ) → ((Γ , A) →ʳ Δ)
(x •ʳ ρ) Z = x
(x •ʳ ρ) (S y) = ρ y

⇑ʳ : ∀{Γ Δ A} → (Γ →ʳ Δ) → (Γ →ʳ (Δ , A))
⇑ʳ ρ x = S (ρ x)

ext : ∀{Γ}{Δ}{A} → (Γ →ʳ Δ) → ((Γ , A) →ʳ (Δ , A))
ext ρ = Z •ʳ ⇑ʳ ρ

idʳ : ∀{Γ} → Γ →ʳ Γ
idʳ x = x

Z-shiftʳ : ∀{Γ}{A}{B} → (Z •ʳ ⇑ʳ idʳ) ≡ idʳ{Γ , A}{B}
Z-shiftʳ {Γ}{A}{B} = extensionality G
  where G : (x : Γ , A ∋ B) → (Z •ʳ ⇑ʳ idʳ) x ≡ idʳ x
        G Z = refl
        G (S x) = refl
{-# REWRITE Z-shiftʳ #-}

