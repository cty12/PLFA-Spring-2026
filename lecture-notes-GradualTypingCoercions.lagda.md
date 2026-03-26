```
open import Data.Bool renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (zero; suc) renaming (ℕ to Nat)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
```

# Gradual Types

```
data Type : Set where
  ℕ    : Type
  ★   : Type
  _⇒_ : Type → Type → Type

-- | Type equality is decidable
_≟ₜ_ : (A B : Type) → Dec (A ≡ B)
ℕ ≟ₜ ℕ = yes refl
ℕ ≟ₜ ★ = no (λ ())
ℕ ≟ₜ (B ⇒ C) = no (λ ())
★ ≟ₜ ℕ = no (λ ())
★ ≟ₜ ★ = yes refl
★ ≟ₜ (B ⇒ C) = no (λ ())
(A ⇒ B) ≟ₜ ℕ = no (λ ())
(A ⇒ B) ≟ₜ ★ = no (λ ())
(A ⇒ B) ≟ₜ (C ⇒ D) with A ≟ₜ C | B ≟ₜ D
... | yes refl | yes refl = yes refl
... | no A≢C | _ = no (λ { refl → A≢C refl })
... | _ | no B≢D = no (λ { refl → B≢D refl })
```

## Type Consistency

```
{- On paper we would just write

 ---------   ------------  ------------
   ℕ ~ ℕ       ★ ~ A        A ~ ★

          A ~ C   B ~ D
      ---------------------
       (A ⇒ B) ~ (C ⇒ D)

This is a more elaborated version that makes it easier
  to write the "coerce" function.
-}
infix 4 _~_

data _~_ : Type → Type → Set where

  ~-ℕ  : ℕ ~ ℕ

  ~-★ : ★ ~ ★

  ★~ℕ : ★ ~ ℕ

  ℕ~★ : ℕ ~ ★

  ★~⇒ : ∀{A B}
    → A ~ ★
    → ★ ~ B
    → ★ ~ (A ⇒ B)

  ⇒~★ : ∀{A B}
    → ★ ~ A
    → B ~ ★
    → (A ⇒ B) ~ ★

  ~-⇒  : ∀ {A B C D}
    → C ~ A
    → B ~ D
    → (A ⇒ B) ~ (C ⇒ D)

~-refl : ∀ {A} → A ~ A
~-refl {A = ℕ}      = ~-ℕ
~-refl {A = ★}     = ~-★
~-refl {A = A ⇒ B} = ~-⇒ ~-refl ~-refl

~-sym : ∀ {A B} → A ~ B → B ~ A
~-sym ~-ℕ = ~-ℕ
~-sym ~-★ = ~-★
~-sym ★~ℕ = ℕ~★
~-sym ℕ~★ = ★~ℕ
~-sym (★~⇒ A~★ ★~B) = ⇒~★ (~-sym A~★) (~-sym ★~B)
~-sym (⇒~★ ★~A B~★) = ★~⇒ (~-sym ★~A) (~-sym B~★)
~-sym (~-⇒ C~A B~D) = ~-⇒ (~-sym C~A) (~-sym B~D)

-- | ★ is consistent with any type
★~ : ∀ A → ★ ~ A
~★ : ∀ A → A ~ ★

★~ ℕ = ★~ℕ
★~ ★ = ~-★
★~ (A ⇒ B) = ★~⇒ (~★ A) (★~ B)
~★ ℕ = ℕ~★
~★ ★ = ~-★
~★ (A ⇒ B) = ⇒~★ (★~ A) (~★ B)
```

# Typing Contexts

```
Var = Nat
Ctx = List Type

data _∋_⦂_ : Ctx → Var → Type → Set where

  Z : ∀ {Γ A}
      ---------------------
    → (A ∷ Γ) ∋ zero ⦂ A

  S : ∀ {Γ A B x}
    → Γ ∋ x ⦂ A
      ------------------------
    → (B ∷ Γ) ∋ suc x ⦂ A
```

# Gradually Typed Lambda Calculus (GTLC)

## Syntax

```
data Term : Set where
  `_    : Var → Term
  $_    : Nat → Term
  ƛ_˙_  : Type → Term → Term
  _·_＠_   : Term → Term → Nat → Term
```

## Typing Rules

```

infix 4 _⊢_⦂_

data _⊢_⦂_ : Ctx → Term → Type → Set where

  ⊢$ : ∀ {Γ n}
      --------------- (T-Const)
    → Γ ⊢ $ n ⦂ ℕ

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      --------------- (T-Var)
    → Γ ⊢ ` x ⦂ A

  ⊢ƛ : ∀ {Γ A N B}
    → (A ∷ Γ) ⊢ N ⦂ B
      --------------------------- (T-Abs)
    → Γ ⊢ ƛ A ˙ N ⦂ (A ⇒ B)

  ⊢· : ∀ {Γ L M A A′ B ℓ}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A′
    → A′ ~ A
      ------------------------------ (T-App)
    → Γ ⊢ (L · M ＠ ℓ) ⦂ B

  ⊢·★ : ∀ {Γ L M A ℓ}
    → Γ ⊢ L ⦂ ★
    → Γ ⊢ M ⦂ A
      ------------------------------ (T-App⋆)
    → Γ ⊢ (L · M ＠ ℓ) ⦂ ★
```

We can prove uniqueness of typing for GTLC.

```
typing-unique : ∀ {Γ M A B}
  → Γ ⊢ M ⦂ A
  → Γ ⊢ M ⦂ B
    ---------------
  → A ≡ B
typing-unique (⊢` ∋x) (⊢` ∋x′) = ∋-unique ∋x ∋x′
  where
  ∋-unique : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
  ∋-unique Z Z = refl
  ∋-unique (S ∋x) (S ∋x′) = ∋-unique ∋x ∋x′
typing-unique ⊢$ ⊢$ = refl
typing-unique (⊢ƛ ⊢N) (⊢ƛ ⊢N′) with typing-unique ⊢N ⊢N′
... | refl = refl
typing-unique (⊢· ⊢L ⊢M A′~A) (⊢· ⊢L′ ⊢M′ C′~C)
    with typing-unique ⊢L ⊢L′
... | refl = refl
typing-unique (⊢· ⊢L ⊢M A′~A) (⊢·★ ⊢L′ ⊢M′)
    with typing-unique ⊢L ⊢L′
... | ()
typing-unique (⊢·★ ⊢L ⊢M) (⊢· ⊢L′ ⊢M′ A′~A)
    with typing-unique ⊢L ⊢L′
... | ()
typing-unique (⊢·★ ⊢L ⊢M) (⊢·★ ⊢L′ ⊢M′) = refl
```

# Coercions

Coercions are combinators that specify the conversion between
two types, so ⊢ c : A ⇒ B.

## Syntax of Coercions

```
infixr 7 _⨟_
infixr 6 _⇒_

data Coercion : Set where

  id  : Type → Coercion

  -- "injection" (tagging)
  _!   : Type → Coercion

  -- "projection" (tag checking)
  _`?_  : Type → Nat → Coercion

  _⇒_  : Coercion → Coercion → Coercion

  _⨟_  : Coercion → Coercion → Coercion
```

## Typing Rules for Coercions

```
-- | We restrict the source of an injection or the target
-- | of a projection to ground types
data Ground : Type → Set where
  G-ℕ  : Ground ℕ
  G-⇒ : Ground (★ ⇒ ★)

infix 4 ⊢_⦂_⇒_

data ⊢_⦂_⇒_ : Coercion → Type → Type → Set where

  ⊢id : ∀ {A}
      --------------------- (T-Id)
    → ⊢ id A ⦂ A ⇒ A

  ⊢! : ∀ {G}
    → Ground G
      --------------------- (T-Inj)
    → ⊢ G ! ⦂ G ⇒ ★

  ⊢? : ∀ {G ℓ}
    → Ground G
      --------------------------------- (T-Proj)
    → ⊢ G `? ℓ ⦂ ★ ⇒ G

  ⊢⇒ : ∀ {A B C D c d}
    → ⊢ c ⦂ C ⇒ A
    → ⊢ d ⦂ B ⇒ D
     ------------------------------------ (T-Fun)
    → ⊢ c ⇒ d ⦂ (A ⇒ B) ⇒ (C ⇒ D)

  ⊢⨟ : ∀ {A B C c d}
    → ⊢ c ⦂ A ⇒ B
    → ⊢ d ⦂ B ⇒ C
      --------------------- (T-Seq)
    → ⊢ c ⨟ d ⦂ A ⇒ C
```

# The Cast Calculus (CC)

## Syntax of CC

```
data Termᶜ : Set where
  `_       : Var → Termᶜ
  $_       : Nat → Termᶜ
  ƛ_˙_     : Type → Termᶜ → Termᶜ
  _·_      : Termᶜ → Termᶜ → Termᶜ
  _⟨_⟩     : Termᶜ → Coercion → Termᶜ
  blame    : (ℓ : Nat) → Termᶜ
```

## Typing Rules for CC

```
infix 4 _⊢ᶜ_⦂_

data _⊢ᶜ_⦂_ : Ctx → Termᶜ → Type → Set where

  ⊢$ : ∀ {Γ n}
      --------------- (T-CC-Const)
    → Γ ⊢ᶜ $ n ⦂ ℕ

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      --------------- (T-CC-Var)
    → Γ ⊢ᶜ ` x ⦂ A

  ⊢ƛ : ∀ {Γ A N B}
    → (A ∷ Γ) ⊢ᶜ N ⦂ B
       --------------------------- (T-CC-Abs)
    → Γ ⊢ᶜ ƛ A ˙ N ⦂ (A ⇒ B)

  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ᶜ L ⦂ (A ⇒ B)
    → Γ ⊢ᶜ M ⦂ A
      --------------------- (T-CC-App)
    → Γ ⊢ᶜ L · M ⦂ B

  ⊢cast : ∀ {Γ M c A B}
    → Γ ⊢ᶜ M ⦂ A
    → ⊢ c ⦂ A ⇒ B
      --------------------------- (T-Cast)
    → Γ ⊢ᶜ M ⟨ c ⟩ ⦂ B

  ⊢blame : ∀ {Γ A ℓ}
      --------------------------- (T-Blame)
    → Γ ⊢ᶜ blame ℓ ⦂ A
```

## Reduction Semantics for CC

Definitions of values and evaluation contexts

```
data Value : Termᶜ → Set where
  V-$      : ∀ {n}     → Value ($ n)
  V-ƛ      : ∀ {A N}   → Value (ƛ A ˙ N)
  V-cast!  : ∀ {V G}   → Value V → Value (V ⟨ G ! ⟩)
  V-cast⇒ : ∀ {V c d} → Value V → Value (V ⟨ c ⇒ d ⟩)

data Frame : Set where
  □·_     : Termᶜ → Frame
  _·□_    : (V : Termᶜ) → Value V → Frame
  □⟨_⟩    : Coercion → Frame

plug : Frame → Termᶜ → Termᶜ
plug (□· M) L = L · M
plug (V ·□ v) M = V · M
plug (□⟨ c ⟩) M = M ⟨ c ⟩
```

Renaming, parallel and single substitutions

```
Rename : Set
Rename = Var → Var

Subst : Set
Subst = Var → Termᶜ

ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → Termᶜ → Termᶜ
rename ρ (` x) = ` (ρ x)
rename ρ ($ n) = $ n
rename ρ (ƛ A ˙ N) = ƛ A ˙ rename (ext ρ) N
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ (M ⟨ c ⟩) = rename ρ M ⟨ c ⟩
rename ρ (blame ℓ) = blame ℓ

exts : Subst → Subst
exts σ zero = ` zero
exts σ (suc x) = rename suc (σ x)

subst : Subst → Termᶜ → Termᶜ
subst σ (` x) = σ x
subst σ ($ n) = $ n
subst σ (ƛ A ˙ N) = ƛ A ˙ subst (exts σ) N
subst σ (L · M) = subst σ L · subst σ M
subst σ (M ⟨ c ⟩) = subst σ M ⟨ c ⟩
subst σ (blame ℓ) = blame ℓ

σ₀ : Termᶜ → Subst
σ₀ M zero = M
σ₀ M (suc x) = ` x

_[_] : Termᶜ → Termᶜ → Termᶜ
N [ M ] = subst (σ₀ M) N
```

Reduction rules

```
infix 4 _—→_

data _—→_ : Termᶜ → Termᶜ → Set where
  ξξ : ∀ {F M N M′ N′}
    → M′ ≡ plug F M
    → N′ ≡ plug F N
    → M —→ N
      ---------------
    → M′ —→ N′

  -- blame propagation
  ξξ-blame : ∀ {F M′ ℓ}
    → M′ ≡ plug F (blame ℓ)
      ------------------------------
    → M′ —→ blame ℓ

  β-ƛ : ∀ {A N V}
    → Value V
      ---------------------------------
    → (ƛ A ˙ N) · V —→ N [ V ]

  -- rules for casts
  β-id : ∀ {A V}
    → Value V
      ---------------------------
    → V ⟨ id A ⟩ —→ V

  β-seq : ∀ {V c d}
    → Value V
      ------------------------------------------------------
    → V ⟨ c ⨟ d ⟩ —→ V ⟨ c ⟩ ⟨ d ⟩

  β-⇒ : ∀ {V W c d}
    → Value V
    → Value W
      ------------------------------------------------------------
    → (V ⟨ c ⇒ d ⟩) · W —→ (V · (W ⟨ c ⟩)) ⟨ d ⟩

  β-proj-inj-ok : ∀ {V G ℓ}
    → Value V
      ------------------------------------------------------
    → V ⟨ G ! ⟩ ⟨ G `? ℓ ⟩ —→ V

  β-proj-inj-bad : ∀ {V G H ℓ}
    → Value V
    → G ≢ H
      ------------------------------------------------------------------
    → V ⟨ G ! ⟩ ⟨ H `? ℓ ⟩ —→ blame ℓ


pattern ξ F M→N  = ξξ {F = F} refl refl M→N
pattern ξ-blame F = ξξ-blame {F = F} refl

```

## Type Safety of CC

Value canonical form lemmas

```
canonical-★-inj : ∀ {V}
  → Value V
  → [] ⊢ᶜ V ⦂ ★
    ---------------------------------------------
  → ∃[ G ] ∃[ W ] Value W × (V ≡ W ⟨ G ! ⟩)
canonical-★-inj (V-cast! {V = W} {G = G} w) (⊢cast _ (⊢! _)) =
  ⟨ G , ⟨ W , ⟨ w , refl ⟩ ⟩ ⟩

canonical-⇒ : ∀ {V A B}
  → Value V
  → [] ⊢ᶜ V ⦂ (A ⇒ B)
    ------------------------------------------------------
  → ∃[ N ] V ≡ ƛ A ˙ N                                ⊎
     ∃[ W ] ∃[ c ] ∃[ d ] Value W × V ≡ W ⟨ c ⇒ d ⟩
canonical-⇒ (V-ƛ {N = N}) (⊢ƛ ⊢N) = inj₁ ⟨ N , refl ⟩
canonical-⇒ (V-cast⇒ {V = W} {c = c} {d = d} w) (⊢cast _ (⊢⇒ _ _)) =
  inj₂ ⟨ W , ⟨ c , ⟨ d , ⟨ w , refl ⟩ ⟩ ⟩ ⟩
```

Progress

```
data Progress (M : Termᶜ) : Set where
  done  : Value M → Progress M
  step  : ∀ {N} → M —→ N → Progress M
  crash : ∀ {ℓ} → M ≡ blame ℓ → Progress M  -- trapped errors

progress : ∀ {M A} → [] ⊢ᶜ M ⦂ A → Progress M
progress (⊢` ())
progress ⊢$ = done V-$
progress (⊢ƛ ⊢M) = done V-ƛ
progress (⊢· {L = L} {M = M} ⊢L ⊢M) =
  case progress ⊢L of λ where
  (step L→L′)  → step (ξ (□· M) L→L′)
  (crash refl) → step (ξ-blame (□· M))
  (done vL) →
    case progress ⊢M of λ where
    (step M→M′)  → step (ξ (L ·□ vL) M→M′)
    (crash refl) → step (ξ-blame (L ·□ vL))
    (done vM) →
      case canonical-⇒ vL ⊢L of λ where
      (inj₁ ⟨ N , refl ⟩) → step (β-ƛ vM)
      (inj₂ ⟨ W , ⟨ c , ⟨ d , ⟨ vW , refl ⟩ ⟩ ⟩ ⟩) → step (β-⇒ vW vM)
progress (⊢cast {c = c} ⊢M ⊢c) =
  case progress ⊢M of λ where
  (step M→M′)  → step (ξ (□⟨ c ⟩) M→M′)
  (crash refl) → step (ξ-blame (□⟨ c ⟩))
  (done vM) →
    case ⊢c of λ where
    ⊢id      → step (β-id vM)
    (⊢! g)   → done (V-cast! vM)
    (⊢⇒ _ _) → done (V-cast⇒ vM)
    (⊢⨟ _ _) → step (β-seq vM)
    (⊢? {G = G} {ℓ = ℓ} g) →
      case canonical-★-inj vM ⊢M of λ where
      ⟨ H , ⟨ W , ⟨ vW , refl ⟩ ⟩ ⟩ →
        case H ≟ₜ G of λ where
        (yes refl) → step (β-proj-inj-ok vW)
        (no H≢G)   → step (β-proj-inj-bad {ℓ = ℓ} vW H≢G)
progress ⊢blame = crash refl
```

Preservation

```
_⦂_⇒ʳ_ : Rename → Ctx → Ctx → Set
ρ ⦂ Γ ⇒ʳ Γ′ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A

_⦂_⇒ˢ_ : Subst → Ctx → Ctx → Set
σ ⦂ Γ ⇒ˢ Γ′ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ⊢ᶜ σ x ⦂ A

⊢ext : ∀ {Γ Γ′ A ρ}
  → ρ ⦂ Γ ⇒ʳ Γ′
  → ext ρ ⦂ (A ∷ Γ) ⇒ʳ (A ∷ Γ′)
⊢ext ⊢ρ Z = Z
⊢ext ⊢ρ (S ∋x) = S (⊢ρ ∋x)

rename-preserve
  : ∀ {Γ Γ′ M A ρ}
  → ρ ⦂ Γ ⇒ʳ Γ′
  → Γ ⊢ᶜ M ⦂ A
  → Γ′ ⊢ᶜ rename ρ M ⦂ A
rename-preserve ⊢ρ (⊢` ∋x) = ⊢` (⊢ρ ∋x)
rename-preserve ⊢ρ ⊢$ = ⊢$
rename-preserve ⊢ρ (⊢ƛ ⊢N) = ⊢ƛ (rename-preserve (⊢ext ⊢ρ) ⊢N)
rename-preserve ⊢ρ (⊢· ⊢L ⊢M) = ⊢· (rename-preserve ⊢ρ ⊢L) (rename-preserve ⊢ρ ⊢M)
rename-preserve ⊢ρ (⊢cast ⊢M ⊢c) = ⊢cast (rename-preserve ⊢ρ ⊢M) ⊢c
rename-preserve ⊢ρ ⊢blame = ⊢blame

⊢exts : ∀ {Γ Γ′ A σ}
  → σ ⦂ Γ ⇒ˢ Γ′
  → exts σ ⦂ (A ∷ Γ) ⇒ˢ (A ∷ Γ′)
⊢exts ⊢σ Z = ⊢` Z
⊢exts ⊢σ (S ∋x) = rename-preserve S (⊢σ ∋x)

subst-preserve
  : ∀ {Γ Γ′ M A σ}
  → σ ⦂ Γ ⇒ˢ Γ′
  → Γ ⊢ᶜ M ⦂ A
  → Γ′ ⊢ᶜ subst σ M ⦂ A
subst-preserve ⊢σ (⊢` ∋x) = ⊢σ ∋x
subst-preserve ⊢σ ⊢$ = ⊢$
subst-preserve ⊢σ (⊢ƛ ⊢N) = ⊢ƛ (subst-preserve (⊢exts ⊢σ) ⊢N)
subst-preserve ⊢σ (⊢· ⊢L ⊢M) = ⊢· (subst-preserve ⊢σ ⊢L) (subst-preserve ⊢σ ⊢M)
subst-preserve ⊢σ (⊢cast ⊢M ⊢c) = ⊢cast (subst-preserve ⊢σ ⊢M) ⊢c
subst-preserve ⊢σ ⊢blame = ⊢blame

sub-preserve
  : ∀ {A B N M}
  → (A ∷ []) ⊢ᶜ N ⦂ B
  → [] ⊢ᶜ M ⦂ A
  → [] ⊢ᶜ N [ M ] ⦂ B
sub-preserve ⊢N ⊢M = subst-preserve (⊢σ₀ ⊢M) ⊢N
  where
  ⊢σ₀ : ∀ {A M} → [] ⊢ᶜ M ⦂ A → σ₀ M ⦂ (A ∷ []) ⇒ˢ []
  ⊢σ₀ ⊢M Z = ⊢M
  ⊢σ₀ ⊢M (S ())
```

```
preserve : ∀ {M N A}
  → [] ⊢ᶜ M ⦂ A
  → M —→ N
    ---------------------
  → [] ⊢ᶜ N ⦂ A

frame-preserve : ∀ {F M N A}
  → [] ⊢ᶜ plug F M ⦂ A
  → M —→ N
    ------------------------
  → [] ⊢ᶜ plug F N ⦂ A

frame-preserve {F = □· M₁}  (⊢· ⊢L ⊢M) L→L′ = ⊢· (preserve ⊢L L→L′) ⊢M
frame-preserve {F = V ·□ _} (⊢· ⊢V ⊢M) M→M′ = ⊢· ⊢V (preserve ⊢M M→M′)
frame-preserve {F = □⟨ c ⟩} (⊢cast ⊢M ⊢c) M→N = ⊢cast (preserve ⊢M M→N) ⊢c

preserve ⊢M (ξξ refl refl M→N)    = frame-preserve ⊢M M→N
preserve (⊢· (⊢ƛ ⊢N) ⊢V) (β-ƛ _)  = sub-preserve ⊢N ⊢V
preserve (⊢cast ⊢V ⊢id) (β-id _)  = ⊢V
preserve (⊢cast ⊢V (⊢⨟ ⊢c ⊢d)) (β-seq _) = ⊢cast (⊢cast ⊢V ⊢c) ⊢d
preserve (⊢· (⊢cast ⊢V (⊢⇒ ⊢c ⊢d)) ⊢W) (β-⇒ _ _) = ⊢cast (⊢· ⊢V (⊢cast ⊢W ⊢c)) ⊢d
preserve (⊢cast (⊢cast ⊢V (⊢! g)) (⊢? _)) (β-proj-inj-ok vV) = ⊢V
preserve ⊢M (β-proj-inj-bad _ _) = ⊢blame
preserve ⊢M (ξξ-blame refl) = ⊢blame

```

# Compilation from GTLC to CC

The coercion function takes two types that are consistent
and returns a coercion. We can prove that the function
always well-typed coercions.

```
coerce : ∀ {A B} → Nat → A ~ B → Coercion
coerce ℓ ~-ℕ = id ℕ
coerce ℓ ~-★ = id ★
coerce ℓ ★~ℕ = ℕ `? ℓ
coerce ℓ ℕ~★ = ℕ !
coerce ℓ (★~⇒ A~★ ★~B) = ((★ ⇒ ★) `? ℓ) ⨟ (coerce ℓ A~★ ⇒ coerce ℓ ★~B)
coerce ℓ (⇒~★ ★~A B~★) = (coerce ℓ ★~A ⇒ coerce ℓ B~★) ⨟ ((★ ⇒ ★) !)
coerce ℓ (~-⇒ c d) = coerce ℓ c ⇒ coerce ℓ d

coerce-wt : ∀ {A B} (ℓ : Nat) (A~B : A ~ B) → ⊢ coerce ℓ A~B ⦂ A ⇒ B
coerce-wt ℓ ~-ℕ = ⊢id
coerce-wt ℓ ~-★ = ⊢id
coerce-wt ℓ ★~ℕ = ⊢? G-ℕ
coerce-wt ℓ ℕ~★ = ⊢! G-ℕ
coerce-wt ℓ (★~⇒ A~★ ★~B) = ⊢⨟ (⊢? G-⇒) (⊢⇒ (coerce-wt ℓ A~★) (coerce-wt ℓ ★~B))
coerce-wt ℓ (⇒~★ ★~A B~★) = ⊢⨟ (⊢⇒ (coerce-wt ℓ ★~A) (coerce-wt ℓ B~★)) (⊢! G-⇒)
coerce-wt ℓ (~-⇒ C~A B~D) = ⊢⇒ (coerce-wt ℓ C~A) (coerce-wt ℓ B~D)

```

The semantics of GTLC is given by compilation to the cast calculus CC
(for which we have already defined the reduction semantics.)


```

compile-∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ A
compile-∋ Z = Z
compile-∋ (S ∋x) = S (compile-∋ ∋x)

compile : ∀ {Γ M A} → Γ ⊢ M ⦂ A → Termᶜ
compile (⊢` {x = x} _) = ` x
compile (⊢$ {n = n}) = $ n
compile (⊢ƛ {A = A} ⊢N) = ƛ A ˙ compile ⊢N
compile (⊢· {ℓ = ℓ} ⊢L ⊢M A′~A) = compile ⊢L · ((compile ⊢M) ⟨ coerce ℓ A′~A ⟩)
compile (⊢·★ {A = A} {ℓ = ℓ} ⊢L ⊢M) =
  (compile ⊢L ⟨ coerce ℓ (★~ (★ ⇒ ★)) ⟩) · (compile ⊢M ⟨ coerce ℓ (~★ A) ⟩)
```

GTLC is type safe because (1) the compilation from GTLC
to CC preserves types and (2) CC is type safe.

```
compile-preserves : ∀ {Γ M A} (⊢M : Γ ⊢ M ⦂ A) → Γ ⊢ᶜ compile ⊢M ⦂ A
compile-preserves (⊢` ∋x) = ⊢` (compile-∋ ∋x)
compile-preserves (⊢$ {n = n}) = ⊢$
compile-preserves (⊢ƛ {A = A} ⊢N) = ⊢ƛ (compile-preserves ⊢N)
compile-preserves (⊢· {ℓ = ℓ} ⊢L ⊢M A′~A) =
  ⊢· (compile-preserves ⊢L)
     (⊢cast (compile-preserves ⊢M) (coerce-wt ℓ A′~A))
compile-preserves (⊢·★ {A = A} {ℓ = ℓ} ⊢L ⊢M) =
  ⊢· (⊢cast (compile-preserves ⊢L) (coerce-wt ℓ (★~ (★ ⇒ ★))))
     (⊢cast (compile-preserves ⊢M) (coerce-wt ℓ (~★ A)))
```
