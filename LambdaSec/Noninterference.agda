{-# OPTIONS --rewriting #-}

module LambdaSec.Noninterference where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

import      LambdaSec.LogicalRelations as LR
import      LambdaSec.Erasure as E
open import LambdaSec.TwoPointLattice using (twoPointLattice; high; low)

open import LambdaSec.LambdaSec twoPointLattice public
module Fundamental = LR twoPointLattice
module Erasure     = E  twoPointLattice


Noninterference : Set
Noninterference =
  ∀ {T} {M : ∅ , T of high ⊢ᵉ `𝔹 of low}
        {V₁ V₂ : ∅ ⊢ᵛ T of high} {V₁′ V₂′ : ∅ ⊢ᵛ `𝔹 of low}
    → M [ val V₁ ] ⇓ V₁′
    → M [ val V₂ ] ⇓ V₂′
      ---------------------------------
    → V₁′ ≡ V₂′

noninterference-LR : Noninterference
noninterference-LR {T} {M} {V₁} {V₂} M[V₁]⇓V₁′ M[V₂]⇓V₂′ =
  Fundamental.fundamental M
    (Fundamental.relSub ((val V₁) • id) ((val V₂) • id) σ₀-rel)
    M[V₁]⇓V₁′ M[V₂]⇓V₂′ ⊑-refl
  where
  high-rel : ∀ T′ {V W} → Fundamental._of_⦂_≈ᵛ⦅_⦆_ T′ high V low W
  high-rel `𝔹                 = λ ()
  high-rel (_ of _ ⇒ _ of _) = λ ()

  σ₀-rel : Fundamental._⊢_≈⦅_⦆_ (∅ , T of high) ((val V₁) • id) low ((val V₂) • id)
  σ₀-rel Z = Fundamental.≈ᵛ→≈ᵉ (high-rel T)
  σ₀-rel (S ())

noninterference-sim : Noninterference
noninterference-sim {M = M} {V₁ = V₁} {V₂ = V₂}
                    {V₁′ = $ b₁ of low} {V₂′ = $ b₂ of low}
                    M[V₁]⇓V₁′ M[V₂]⇓V₂′
  = go sim₁ sim₂
  where
  go : Erasure._⇓ₑ_
         (Erasure._[_]ₑ
           (Erasure.erase M low (low Erasure.⊑? low))
           (Erasure.eraseᵛ V₁ low (high Erasure.⊑? low)))
         (Erasure.eraseᵛ ($ b₁ of low) low (low Erasure.⊑? low))
     → Erasure._⇓ₑ_
         (Erasure._[_]ₑ
           (Erasure.erase M low (low Erasure.⊑? low))
           (Erasure.eraseᵛ V₂ low (high Erasure.⊑? low)))
         (Erasure.eraseᵛ ($ b₂ of low) low (low Erasure.⊑? low))
       ---------------------------------
     → ($ b₁ of low) ≡ ($ b₂ of low)
  go sim₁ sim₂ with Erasure.⇓ₑ-deterministic sim₁ sim₂
  ... | refl = refl

  sim₁ : Erasure._⇓ₑ_
           (Erasure._[_]ₑ
             (Erasure.erase M low (low Erasure.⊑? low))
             (Erasure.eraseᵛ V₁ low (high Erasure.⊑? low)))
           (Erasure.eraseᵛ ($ b₁ of low) low (low Erasure.⊑? low))
  sim₁ = subst
           (λ □ → Erasure._⇓ₑ_ □
                     (Erasure.eraseᵛ ($ b₁ of low) low (low Erasure.⊑? low)))
           (Erasure.erase-[] {N = M} {V = V₁} {ζ = low})
           (Erasure.sim M[V₁]⇓V₁′)

  sim₂ : Erasure._⇓ₑ_
           (Erasure._[_]ₑ
             (Erasure.erase M low (low Erasure.⊑? low))
             (Erasure.eraseᵛ V₂ low (high Erasure.⊑? low)))
           (Erasure.eraseᵛ ($ b₂ of low) low (low Erasure.⊑? low))
  sim₂ = subst
           (λ □ → Erasure._⇓ₑ_ □
                     (Erasure.eraseᵛ ($ b₂ of low) low (low Erasure.⊑? low)))
           (Erasure.erase-[] {N = M} {V = V₂} {ζ = low})
           (Erasure.sim M[V₂]⇓V₂′)
