{-# OPTIONS --rewriting #-}

module LambdaSec.Noninterference where

open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import LambdaSec.TwoPointLattice using (twoPointLattice; high; low)

open import LambdaSec.LambdaSec twoPointLattice public
open import LambdaSec.LogicalRelations twoPointLattice
  using (fundamental; relSub; _of_⦂_≈ᵛ⦅_⦆_; _⊢_≈⦅_⦆_; ≈ᵛ→≈ᵉ)
open import LambdaSec.Simulation twoPointLattice
  using (erase; eraseᵛ; erase-[]; sim; _[_]ₑ; _⇓ₑ_; ⇓ₑ-deterministic)


-- | The main security theorem: NI
Noninterference = ∀ {M : ∅ , `𝔹 of high ⊢ᵉ `𝔹 of low}
                    {V₁ V₂ : ∅ ⊢ᵛ `𝔹 of high} {V₁′ V₂′}
    → M [ val V₁ ] ⇓ V₁′
    → M [ val V₂ ] ⇓ V₂′
      ---------------------------------
    → V₁′ ≡ V₂′

-- | Two flavors of the NI proof
noninterference-LR noninterference-sim : Noninterference

-- | The logical relations version of the proof
noninterference-LR {M} {V₁} {V₂} M[V₁]⇓V₁′ M[V₂]⇓V₂′ =
  fundamental M (relSub ((val V₁) • id) ((val V₂) • id) σ₀-rel)
              M[V₁]⇓V₁′ M[V₂]⇓V₂′ ⊑-refl
  where
  σ₀-rel : ∅ , _ of high ⊢ (val V₁) • id ≈⦅ low ⦆ (val V₂) • id
  σ₀-rel Z = ≈ᵛ→≈ᵉ (λ ())

-- | The simulation version of the proof
noninterference-sim {M} {V₁} {V₂} {V₁′ = $ b₁ of low} {V₂′ = $ b₂ of low}
                    M[V₁]⇓V₁′ M[V₂]⇓V₂′ =
  let sim₁ : erase M low _ [ eraseᵛ V₁ low (high ⊑? low) ]ₑ ⇓ₑ
             eraseᵛ ($ b₁ of low) low (low ⊑? low)
      sim₁ = sim M[V₁]⇓V₁′
      sim₂ = sim M[V₂]⇓V₂′ in
  case ⇓ₑ-deterministic sim₁ sim₂ of λ where
  refl → refl
