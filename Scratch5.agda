{-# OPTIONS --rewriting #-}
module Scratch5 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
 using (_≡_; refl; sym; cong; cong₂)

open import lecture-notes-Substitution
open import STLC-Reduction

-- example of a logical relation
ℰ : (A : Type) → ∅ ⊢ A → Set
𝒱 : (A : Type) → ∅ ⊢ A → Set

ℰ A M = Σ[ V ∈ ∅ ⊢ A ] (M —↠ V) × (Value V) × (𝒱 A V)

𝒱 (A ⇒ B) (ƛ N) = ∀ (W : ∅ ⊢ A) → 𝒱 A W → ℰ B (N [ W ])
𝒱 (A ⇒ B) (L · M) = ⊥
𝒱 `ℕ (L · M) = ⊥
𝒱 `ℕ `zero = ⊤

-- well-behaved substitution
_⊢ˢ_ : (Γ : Context) → (Γ →ˢ ∅) → Set
Γ ⊢ˢ σ = (∀ {C : Type} (x : Γ ∋ C) → 𝒱 C (σ x))

𝒱→Value : ∀{A}{M : ∅ ⊢ A} → 𝒱 A M → Value M
𝒱→Value {A} {ƛ M} wtv = V-ƛ
𝒱→Value {A ⇒ B} {L · M} ()
𝒱→Value {`ℕ} {L · M} ()
𝒱→Value {A} {`zero} wtv = V-zero

𝒱→ℰ : ∀{A}{M : ∅ ⊢ A} → 𝒱 A M → ℰ A M
𝒱→ℰ {A}{M} wtv = ⟨ M , ⟨ (M ∎) , ⟨ 𝒱→Value wtv , wtv ⟩ ⟩ ⟩

extend-sub : ∀{A}{V : ∅ ⊢ A}{Γ}{σ : Γ →ˢ ∅}
         → 𝒱 A V   →   Γ ⊢ˢ σ
         → (Γ , A) ⊢ˢ (V • σ)
extend-sub {A} {V} wbv ⊢σ {C} Z = wbv
extend-sub {A} {V} wbv ⊢σ {C} (S x) = ⊢σ x

app-compat : ∀{A}{B} {L L'  : ∅ ⊢ A ⇒ B}{M M' : ∅ ⊢ A}
           → L —↠ L'
           → Value L'
           → M —↠ M'
           → L · M —↠ L' · M'
app-compat {A}{B}{L}{L}{M}{M} (L ∎) vL (M ∎) = L · M ∎
app-compat {A}{B}{L}{L}{M}{M''} (L ∎) vL (step—→ M {M'} M'→M'' M→M') =
  begin
     L · M     —→⟨ ξ-·₂ vL M→M' ⟩
     L · M'    —↠⟨ app-compat (L ∎) vL M'→M'' ⟩
     L · M''
  ∎
app-compat {A}{B}{L}{L''}{M}{M'}(step—→ L {L'}{L''} L'→L'' L→L' ) vL' M→M' =
  begin
    L · M             —→⟨ ξ-·₁ L→L' ⟩
    L' · M            —↠⟨ app-compat L'→L'' vL' M→M' ⟩
    L'' · M'
  ∎

-- generalized terminate to allow free variables
-- introduce a closing substitution
fundamental-property : ∀ {A}{Γ} {σ : Γ →ˢ ∅}
  → (M : Γ ⊢ A)
  → Γ ⊢ˢ σ
  → ℰ A (subst σ M)
fundamental-property (` ∋x) ⊢σ =
  let v = ⊢σ ∋x in
  𝒱→ℰ v
fundamental-property {A ⇒ B}{Γ}{σ} (ƛ N) ⊢σ =
   ⟨ subst σ (ƛ N) , ⟨ (subst σ (ƛ N) ∎) , ⟨ V-ƛ , Goal ⟩ ⟩ ⟩
   where
   Goal : (W : ∅ ⊢ A) → 𝒱 A W → ℰ B (subst (exts σ) N [ W ])
   Goal W vW =
     let IH = fundamental-property{σ = W • σ} N (extend-sub vW ⊢σ) in
     IH -- implicitly uses exts-sub-cons!
   
fundamental-property `zero ⊢σ = ⟨ `zero , ⟨ (`zero ∎) , ⟨ V-zero , tt ⟩ ⟩ ⟩
fundamental-property {σ = σ} (L · M) ⊢σ
    with fundamental-property L ⊢σ
... | ⟨ V , ⟨ σL→V , ⟨ vV , wbV ⟩ ⟩ ⟩
    with fundamental-property M ⊢σ
... | ⟨ W , ⟨ σM→W , ⟨ vW , wbW ⟩ ⟩ ⟩
    with vV
... | V-ƛ{N = N}
    with wbV W wbW
... | ⟨ Q , ⟨ N[W]→Q , ⟨ vQ , wbQ ⟩ ⟩ ⟩ =
      ⟨ Q , ⟨ R , ⟨ vQ , wbQ ⟩ ⟩ ⟩
    where
    R : subst σ L · subst σ M —↠ Q
    R =   begin
          subst σ L · subst σ M     —↠⟨ app-compat σL→V vV σM→W ⟩
          (ƛ N) · W                 —→⟨ β-ƛ vW ⟩
          N [ W ]                   —↠⟨ N[W]→Q ⟩
          Q                         ∎

terminate : ∀ {A}
  → (M : ∅ ⊢ A)
  → Σ[ V ∈ ∅ ⊢ A ] (M —↠ V) × Value V
terminate {A} ⊢M 
    with fundamental-property{A}{∅}{id} ⊢M (λ ())
... | ⟨ V , ⟨ M—↠V , ⟨ vV , 𝒱V ⟩ ⟩ ⟩ =
      ⟨ V , ⟨ M—↠V , vV ⟩ ⟩
