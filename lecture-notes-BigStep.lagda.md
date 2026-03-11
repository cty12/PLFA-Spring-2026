```
{-# OPTIONS --rewriting #-}
module lecture-notes-BigStep where
```

# Imports

```agda
open import Data.Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong-app)
open import Data.Product.Base using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function.Base using (_∘_)
open import lecture-notes-Untyped
  using (Var; Term; `_; ′_; ƛ_; _·_; subst; subst-zero; exts; rename; _[_];
       β; ξ₁; ξ₂; ζ; _—→_; _—↠_; step—→; _—→⟨_⟩_; _∎; —↠-trans; appL-cong; app-cong; lam-cong;
       Neutral; Normal; Rename; Subst)
```

```agda
infix 5 _⇓_
data _⇓_ : Term → Term → Set where

  ⇓-var : ∀{x : Var}
    → ` x ⇓ ` x
    
  ⇓-lam : ∀{N N′ : Term}
    → N ⇓ N′
    → ƛ N ⇓ ƛ N′

  ⇓-app : ∀{L M : Term}{N : Term}{V}
    → L ⇓ (ƛ N)
    → N [ M ] ⇓ V
    -------------
    → L · M ⇓ V

  ⇓-app-neutral : ∀{L M : Term}{L′ M′ : Term}
    → L ⇓ L′
    → Neutral L′
    → M ⇓ M′
    -----------------
    → L · M ⇓ L′ · M′
```

```agda
big-step-to-reduction : ∀{M N : Term}
  → M ⇓ N
  → M —↠ N
big-step-to-reduction (⇓-var{x}) = ` x ∎
big-step-to-reduction (⇓-lam{N}{N′} N⇓N′) =
  let IH : N —↠ N′
      IH = big-step-to-reduction N⇓N′ in
  lam-cong IH
big-step-to-reduction (⇓-app{L}{M}{N}{V} L⇓λN NM⇓V) =
  let IH1 : L —↠ ƛ N
      IH1 = big-step-to-reduction L⇓λN in
  let IH2 : (N [ M ]) —↠ V
      IH2 = big-step-to-reduction NM⇓V in
  let s1 : L · M —↠ (ƛ N) · M
      s1 = appL-cong IH1 in
  let s2 : (ƛ N) · M —↠ N [ M ]
      s2 = (ƛ N) · M —→⟨ β ⟩ N [ M ] ∎ in   
  —↠-trans s1 (—↠-trans s2 IH2)
big-step-to-reduction (⇓-app-neutral L⇓ nL′ M⇓) =
  let IH1 = big-step-to-reduction L⇓ in
  let IH2 = big-step-to-reduction M⇓ in
  app-cong IH1 IH2
```

```agda
data Lam : Term → Set where
  ƛ_ : ∀{N} → Lam (ƛ N)
```

```agda
big-normal : ∀ {M M′ : Term} → M ⇓ M′ → Normal M′
big-normal (⇓-var{x}) = ′ (` x)
big-normal (⇓-lam M⇓M′) = ƛ big-normal M⇓M′
big-normal (⇓-app M⇓M′ M⇓M′₁) = big-normal M⇓M′₁
big-normal (⇓-app-neutral L⇓L′ nL M⇓M′) = ′ (nL · (big-normal M⇓M′))
```

```agda
normal-big-id : ∀ {M : Term} → Normal M → M ⇓ M
normal-big-id {` x} (′ (` x)) = ⇓-var
normal-big-id {L · M} (′ (nL · nM)) =
  ⇓-app-neutral (normal-big-id (′ nL)) nL (normal-big-id nM)
normal-big-id {M} (ƛ n) = ⇓-lam (normal-big-id n)
```

```agda
big-sub-inv : ∀ (N : Term) {M : Term}{σ : Subst}
  → subst σ N ⇓ M
  → ∃[ N′ ] N ⇓ N′ × subst σ N′ ⇓ M
big-sub-inv (` x) sN⇓ = ⟨ (` x) , ⟨ ⇓-var , sN⇓ ⟩ ⟩
big-sub-inv (ƛ N) (⇓-lam sN⇓)
    with big-sub-inv N sN⇓
... | ⟨ N′ , ⟨ N′⇓ , sN′⇓ ⟩ ⟩ = ⟨ ƛ N′ , ⟨ ⇓-lam N′⇓ , ⇓-lam sN′⇓ ⟩ ⟩
big-sub-inv (L · M) (⇓-app{N = N} sL⇓ sM⇓)
    with big-sub-inv L sL⇓
... | ⟨ L′ , ⟨ L′⇓ , sL′⇓ ⟩ ⟩
    with big-sub-inv N sM⇓
... | ⟨ N′ , ⟨ N′⇓ , sN′⇓ ⟩ ⟩
    with big-normal L′⇓
... | ′ nL = {!!}
... | ƛ N₁ = ⟨ {!!} , ⟨ (⇓-app L′⇓ {!!}) , {!!} ⟩ ⟩


big-sub-inv (L · M) (⇓-app-neutral sN⇓ x sN⇓₁) = {!!}

```

```agda
sub-step : ∀{N M M′ N′ : Term}
  → N [ M′ ] ⇓ N′
  → M —→ M′
  → N [ M ] ⇓ N′
sub-step NM⇓ M→M′ = {!!}
```

```agda
step-big-step : ∀{L M N : Term}
  → L —→ M
  → M ⇓ N
  → L ⇓ N
step-big-step {L · M} {LM} {N} (ξ₁ L→L′) (⇓-app L′⇓λN M⇓N₁) =
  let IH = step-big-step L→L′ L′⇓λN in -- L ⇓ ƛ N₁
  ⇓-app IH M⇓N₁
step-big-step {L · M} {LM} {N} (ξ₁ L→L′) (⇓-app-neutral L′⇓ n M⇓M′) =
  let IH = step-big-step L→L′ L′⇓ in
  ⇓-app-neutral IH n M⇓M′
step-big-step {L · M} {LM} {N} (ξ₂ M→M′) (⇓-app{N = N₁} L⇓ NM⇓) =
  ⇓-app L⇓ (sub-step{N = N₁} NM⇓ M→M′)
step-big-step {L} {M} {N} (ξ₂ L→M) (⇓-app-neutral M⇓N x M⇓N₁) =
  ⇓-app-neutral M⇓N x (step-big-step L→M M⇓N₁)
step-big-step {(ƛ N) · M} {R} {N′} β M⇓N
    with big-sub-inv N M⇓N
... | ⟨ N′ , ⟨ N′⇓ , sN′⇓ ⟩ ⟩ = ⇓-app (⇓-lam N′⇓) sN′⇓
step-big-step {ƛ L} {ƛ L′} {ƛ N} (ζ L→M) (⇓-lam M⇓N) =
    ⇓-lam (step-big-step L→M M⇓N)
```

```agda
reduction-to-big-step : ∀{M N : Term}
  → M —↠ N
  → Normal N
  → M ⇓ N
reduction-to-big-step (_ ∎) n = normal-big-id n
reduction-to-big-step (step—→ L {M}{N} M—↠N L→M) lam =
  let IH : M ⇓ N
      IH = reduction-to-big-step M—↠N lam in
  step-big-step L→M IH
```
