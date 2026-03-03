```
module lecture-notes-GradualTyping where
```

# Gradually Typed Lambda Calculus

## Imports

```
open import Data.Bool renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

```

## Primitives

The idea here is to use Agda values as primitive constants. We include
natural numbers, Booleans, and Agda functions over naturals and
Booleans.

The `Base` and `Prim` data types describe the types of constants.

```
data Base : Set where
  B-Nat : Base
  B-Bool : Base

data Prim : Set where
  base : Base → Prim
  _⇒_ : Base → Prim → Prim
```

The `base-rep` and `rep` functions map from the type descriptors to
the Agda types that we will use to represent the constants.

```
base-rep : Base → Set 
base-rep B-Nat = ℕ
base-rep B-Bool = 𝔹

rep : Prim → Set
rep (base b) = base-rep b
rep (b ⇒ p) = base-rep b → rep p
```

## Types

```
data BaseTy : Set where
  Nat : BaseTy
  Bool : BaseTy

data Type : Set where
  `_    : BaseTy → Type
  ⋆     : Type
  _⇒_   : Type → Type → Type
  _`×_  : Type → Type → Type
  _`⊎_  : Type → Type → Type
```

## Consistency and Join

```
infix  5  _~_
data _~_ : Type → Type → Set where
  unk~L : ∀ {A} → ⋆ ~ A
  unk~R : ∀ {A} → A ~ ⋆
  base~ : ∀{ι} → ` ι ~ ` ι
  fun~ : ∀{A B A' B'}
    → A' ~ A  →  B ~ B'
      -------------------
    → (A ⇒ B) ~ (A' ⇒ B')
  pair~ : ∀{A B A' B'}
    → A ~ A'  →  B ~ B'
      -------------------
    → (A `× B) ~ (A' `× B')
  sum~ : ∀{A B A' B'}
    → A ~ A'  →  B ~ B'
      -------------------
    → (A `⊎ B) ~ (A' `⊎ B')
```

```
~-refl : ∀{A} → A ~ A
~-refl {` ι} = base~
~-refl {⋆} = unk~L
~-refl {A ⇒ B} = fun~ ~-refl ~-refl
~-refl {A `× B} = pair~ ~-refl ~-refl
~-refl {A `⊎ B} = sum~ ~-refl ~-refl
```

```
~-sym : ∀{A B} → A ~ B → B ~ A
~-sym {A} {B} unk~L = unk~R
~-sym {A} {B} unk~R = unk~L
~-sym {A} {B} base~ = base~
~-sym {A} {B} (fun~ ab ab₁) = fun~ (~-sym ab) (~-sym ab₁)
~-sym {A} {B} (pair~ ab ab₁) = pair~ (~-sym ab) (~-sym ab₁)
~-sym {A} {B} (sum~ ab ab₁) = sum~ (~-sym ab) (~-sym ab₁)
```

```
⨆ : ∀{A B : Type} → (c : A ~ B) → Type
⨆ {.⋆} {B} unk~L = B
⨆ {A} {.⋆} unk~R = A
⨆ {(` ι)} {.(` _)} base~ = ` ι
⨆ {.(_ ⇒ _)} {.(_ ⇒ _)} (fun~ c d) = (⨆ c) ⇒ (⨆ d)
⨆ {.(_ `× _)} {.(_ `× _)} (pair~ c d) = (⨆ c) `× (⨆ d)
⨆ {.(_ `⊎ _)} {.(_ `⊎ _)} (sum~ c d) = (⨆ c) `⊎ (⨆ d)
```

## Terms

```
infix  5  ƛ_˙_
infixl 7  _·_
infix  9  `_

Id : Set
Id = ℕ

data Term : Set where
  $                     : (p : Prim) → rep p → Term
  `_                    :  Id → Term
  ƛ_˙_                  :  Type → Term → Term
  _·_                   :  Term → Term → Term
  pair                  :  Term → Term → Term
  fst                   :  Term → Term
  snd                   :  Term → Term
  inl                   :  Term → Term
  inr                   :  Term → Term
  case                  :  Term → Term → Term → Term
  _⦂_                   : Term → Type → Term
```

## Type of a primitive

```
typeof-base : Base → Type
typeof-base B-Nat = ` Nat
typeof-base B-Bool = ` Bool

typeof : Prim → Type
typeof (base b) = typeof-base b 
typeof (b ⇒ p) = typeof-base b ⇒ typeof p
```

## Contexts

```
Context : Set
Context = List Type
```

```
infix  4  _∋_⦂_
_∋_⦂_ : Context → ℕ → Type → Set
[] ∋ x ⦂ A = ⊥
(B ∷ Γ) ∋ zero ⦂ A = A ≡ B
(B ∷ Γ) ∋ suc x ⦂ A = Γ ∋ x ⦂ A
```

## Type Matching

```
data _▹_⇒_ : Type → Type → Type → Set where
  match⇒⇒ : ∀{A B} → (A ⇒ B) ▹ A ⇒ B
  match⇒⋆ : ⋆ ▹ ⋆ ⇒ ⋆

data _▹_×_ : Type → Type → Type → Set where
  match×× : ∀{A B} → (A `× B) ▹ A × B
  match×⋆ : ⋆ ▹ ⋆ × ⋆

data _▹_⊎_ : Type → Type → Type → Set where
  match⊎⊎ : ∀{A B} → (A `⊎ B) ▹ A ⊎ B
  match⊎⋆ : ⋆ ▹ ⋆ ⊎ ⋆
```

## Typing judgement

```
infix  4  _⊢G_⦂_

data _⊢G_⦂_ : Context → Term → Type → Set where

  -- Axiom 
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢G ` x ⦂ A

  -- ⇒-I 
  ⊢ƛ : ∀ {Γ N A B}
    → A ∷ Γ ⊢G N ⦂ B
      -------------------
    → Γ ⊢G (ƛ A ˙ N) ⦂ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ L M A A₁ A₂ B}
    → Γ ⊢G L ⦂ A
    → Γ ⊢G M ⦂ B
    → A ▹ A₁ ⇒ A₂
    → B ~ A₁
      --------------
    → Γ ⊢G L · M ⦂ A₂

  ⊢$ : ∀{Γ p k A}
     → A ≡ typeof p
       -------------
     → Γ ⊢G $ p k ⦂ A

  ⊢pair : ∀ {Γ A B}{M N : Term}
    → Γ ⊢G M ⦂ A  →  Γ ⊢G N ⦂ B
      -----------------------
    → Γ ⊢G (pair M N) ⦂ A `× B
    
  ⊢fst : ∀ {Γ A A₁ A₂}{M : Term}
    → Γ ⊢G M ⦂ A
    → A ▹ A₁ × A₂
      -------------------------
    → Γ ⊢G fst M ⦂ A₁

  ⊢snd : ∀ {Γ A A₁ A₂}{M : Term}
    → Γ ⊢G M ⦂ A
    → A ▹ A₁ × A₂
      -------------------------
    → Γ ⊢G (snd M) ⦂ A₂

  ⊢inl : ∀ {Γ A}{M : Term}
    → (B : Type)
    → Γ ⊢G M ⦂ A
      -----------------------
    → Γ ⊢G (inl M) ⦂ A `⊎ B

  ⊢inr : ∀ {Γ B}{M : Term}
    → (A : Type)
    → Γ ⊢G M ⦂ B
      -----------------------
    → Γ ⊢G (inr M) ⦂ A `⊎ B

  ⊢case : ∀{Γ A A₁ A₂ B B₁ B₂ C C₁ C₂}{L M N : Term}
    → Γ ⊢G L ⦂ A
    → Γ ⊢G M ⦂ B
    → Γ ⊢G N ⦂ C
    → {A ▹ A₁ ⊎ A₂ }
    → {B ▹ B₁ ⇒ B₂ }
    → {C ▹ C₁ ⇒ C₂ }
    → {A₁ ~ B₁}
    → {A₂ ~ C₁}
    → {bc : B₂ ~ C₂}
      ----------------------------------
    → Γ ⊢G (case L M N) ⦂ ⨆ bc

  ⊢⦂ : ∀{Γ M A B}
    → Γ ⊢G M ⦂ A
    → {A ~ B}
      -------------------
    → Γ ⊢G (M ⦂ B) ⦂ B
```

## Cast Calculus

```
data CCTerm : Set where
  $                     : (p : Prim) → rep p → CCTerm
  `_                    : Id → CCTerm
  ƛ_˙_                  : Type → CCTerm → CCTerm
  _·_                   : CCTerm → CCTerm → CCTerm
  pair                  : CCTerm → CCTerm → CCTerm
  fst                   : CCTerm → CCTerm
  snd                   : CCTerm → CCTerm
  inl                   : CCTerm → CCTerm
  inr                   : CCTerm → CCTerm
  case                  : CCTerm → CCTerm → CCTerm → CCTerm
  _⟨_⇒_⟩                : CCTerm → Type → Type → CCTerm
  blame                 : CCTerm
```

## Typing judgement

```
infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → CCTerm → Type → Set where

  -- Axiom 
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I 
  ⊢ƛ : ∀ {Γ N A B}
    → A ∷ Γ ⊢ N ⦂ B
      -------------------
    → Γ ⊢ (ƛ A ˙ N) ⦂ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      --------------
    → Γ ⊢ L · M ⦂ B

  ⊢$ : ∀{Γ p k A}
     → A ≡ typeof p
       -------------
     → Γ ⊢ $ p k ⦂ A

  ⊢pair : ∀ {Γ A B}{M N : CCTerm}
    → Γ ⊢ M ⦂ A  →  Γ ⊢ N ⦂ B
      -----------------------
    → Γ ⊢ (pair M N) ⦂ A `× B
    
  ⊢fst : ∀ {Γ A₁ A₂}{M : CCTerm}
    → Γ ⊢ M ⦂ A₁ `× A₂
      -------------------------
    → Γ ⊢ fst M ⦂ A₁

  ⊢snd : ∀ {Γ A₁ A₂}{M : CCTerm}
    → Γ ⊢ M ⦂ A₁ `× A₂
      -------------------------
    → Γ ⊢ (snd M) ⦂ A₂

  ⊢inl : ∀ {Γ A}{M : CCTerm}
    → (B : Type)
    → Γ ⊢ M ⦂ A
      -----------------------
    → Γ ⊢ (inl M) ⦂ A `⊎ B

  ⊢inr : ∀ {Γ B}{M : CCTerm}
    → (A : Type)
    → Γ ⊢ M ⦂ B
      -----------------------
    → Γ ⊢ (inr M) ⦂ A `⊎ B

  ⊢case : ∀{Γ A₁ A₂ B}{L M N : CCTerm}
    → Γ ⊢ L ⦂ A₁ `⊎ A₂
    → Γ ⊢ M ⦂ A₁ ⇒ B
    → Γ ⊢ N ⦂ A₂ ⇒ B
      ---------------------
    → Γ ⊢ (case L M N) ⦂ B

  ⊢⟨⟩ : ∀{Γ M A B}
    → Γ ⊢ M ⦂ A
    → {A ~ B}
      -------------------
    → Γ ⊢ (M ⟨ A ⇒ B ⟩) ⦂ B
```

## Matching

```
match⇒-~ : ∀{A A₁ A₂}
  → A ▹ A₁ ⇒ A₂
  → A ~ (A₁ ⇒ A₂)
match⇒-~ {⋆} {A₁} {A₂} A▹A₁⇒A₂ = unk~L
match⇒-~ {A ⇒ A₃} {A₁} {A₂} match⇒⇒ = ~-refl

match×-~ : ∀{A A₁ A₂}
  → A ▹ A₁ × A₂
  → A ~ (A₁ `× A₂)
match×-~ {A} match×× = ~-refl
match×-~ {A} match×⋆ = unk~L

match⊎-~ : ∀{A A₁ A₂}
  → A ▹ A₁ ⊎ A₂
  → A ~ (A₁ `⊎ A₂)
match⊎-~ {A} match⊎⊎ = ~-refl
match⊎-~ {A} match⊎⋆ = unk~L
```

```
~-⨆-right : ∀{B₂ C₂}
  → (bc : B₂ ~ C₂)
  → ⨆ bc ~ C₂

~-⨆-left : ∀{B₂ C₂}
  → (bc : B₂ ~ C₂)
  → B₂ ~ ⨆ bc
~-⨆-left unk~L = unk~L
~-⨆-left unk~R = ~-refl
~-⨆-left base~ = base~
~-⨆-left (fun~ bc bc₁) = fun~ (~-⨆-right bc) (~-⨆-left bc₁)
~-⨆-left (pair~ bc bc₁) = pair~ (~-⨆-left bc) (~-⨆-left bc₁)
~-⨆-left (sum~ bc bc₁) = sum~ (~-⨆-left bc) (~-⨆-left bc₁)

~-⨆-right unk~L = ~-refl
~-⨆-right unk~R = unk~R
~-⨆-right base~ = base~
~-⨆-right (fun~ bc bc₁) = fun~ (~-⨆-left bc) (~-⨆-right bc₁)
~-⨆-right (pair~ bc bc₁) = pair~ (~-⨆-right bc) (~-⨆-right bc₁)
~-⨆-right (sum~ bc bc₁) = sum~ (~-⨆-right bc) (~-⨆-right bc₁)

match-~-⨆ : ∀{A₁ B B₁ B₂ C₂}
  → B ▹ B₁ ⇒ B₂
  → (bc : B₂ ~ C₂)
  → (A₁ ~ B₁)
  → B ~ (A₁ ⇒ ⨆ bc)
match-~-⨆ {A₁} {B} {B₁} {B₂} {C₂} match⇒⇒ bc ab = fun~ ab (~-⨆-left bc)
match-~-⨆ {A₁} {B} {B₁} {B₂} {C₂} match⇒⋆ bc ab = unk~L
```

## Compile from GTCL to CC

```
compile : ∀{Γ A}{M : Term} → Γ ⊢G M ⦂ A → ∃[ M′ ] Γ ⊢ M′ ⦂ A
compile {Γ} {A} {M} (⊢`{x = x} ∋x) = ⟨ ` x , ⊢` ∋x ⟩
compile {Γ} {A ⇒ B} {M} (⊢ƛ ⊢M)
    with compile ⊢M
... | ⟨ M′ , ⊢M′ ⟩ = ⟨ ƛ A ˙ M′ , ⊢ƛ ⊢M′ ⟩
compile {Γ} {A₂} {L · M} (⊢·{A = A}{A₁}{A₂}{B} ⊢L ⊢M A▹A₁⇒A₂ B~A₁)
    with compile ⊢L | compile ⊢M 
... | ⟨ L′ , ⊢L′ ⟩ | ⟨ M′ , ⊢M′ ⟩ =
    let ⊢L″ = ⊢⟨⟩ ⊢L′ {match⇒-~ A▹A₁⇒A₂} in
    let ⊢M″ = ⊢⟨⟩ ⊢M′ {B~A₁} in
    ⟨ (L′ ⟨ A ⇒ (A₁ ⇒ A₂) ⟩) · (M′ ⟨ B ⇒ A₁ ⟩) , ⊢· ⊢L″ ⊢M″ ⟩
compile {Γ} {A} {$ p k} (⊢$ refl) = ⟨ ($ p k) , (⊢$ refl) ⟩
compile {Γ} {A} {M} (⊢pair ⊢M ⊢N)
    with compile ⊢M | compile ⊢N 
... | ⟨ M′ , ⊢M′ ⟩ | ⟨ N′ , ⊢N′ ⟩ = ⟨ pair M′ N′ , ⊢pair ⊢M′ ⊢N′ ⟩
compile {Γ} {A₁} {M} (⊢fst{A = A}{A₁}{A₂} ⊢M A▹A₁×A₂)
    with compile ⊢M
... | ⟨ M′ , ⊢M′ ⟩ =
    ⟨ fst (M′ ⟨ A ⇒ A₁ `× A₂ ⟩) , (⊢fst (⊢⟨⟩ ⊢M′ {match×-~ A▹A₁×A₂})) ⟩
compile {Γ} {A₂} {M} (⊢snd{A = A}{A₁}{A₂} ⊢M A▹A₁×A₂)
    with compile ⊢M
... | ⟨ M′ , ⊢M′ ⟩ =
    ⟨ snd (M′ ⟨ A ⇒ A₁ `× A₂ ⟩) , (⊢snd (⊢⟨⟩ ⊢M′ {match×-~ A▹A₁×A₂})) ⟩
compile {Γ} {A₁ `⊎ B} {inl M} (⊢inl B ⊢M)
    with compile ⊢M
... | ⟨ M′ , ⊢M′ ⟩ =
    ⟨ inl M′ , ⊢inl B ⊢M′ ⟩
compile {Γ} {A₁ `⊎ B} {inr M} (⊢inr A₁ ⊢M)
    with compile ⊢M
... | ⟨ M′ , ⊢M′ ⟩ =
    ⟨ inr M′ , ⊢inr A₁ ⊢M′ ⟩
compile {Γ} {A′} {case L M N}
    (⊢case{A = A}{A₁}{A₂}{B}{B₁}{B₂}{C}{C₁}{C₂} ⊢L ⊢M ⊢N {a12}{b12}{c12}{a1b1}{b2c1}{bc})
    with compile ⊢L | compile ⊢M | compile ⊢N
... | ⟨ L′ , ⊢L′ ⟩ | ⟨ M′ , ⊢M′ ⟩ | ⟨ N′ , ⊢N′ ⟩ =
    let c1 : B ~ (A₁ ⇒ ⨆ bc)
        c1 = match-~-⨆ b12 bc a1b1 in
    let c2 : C ~ (A₂ ⇒ ⨆ bc)
        c2 = match-~-⨆{A₂}{C}{C₁}{?}{A} c12 (~-sym {!!}) b2c1 in
    ⟨ case (L′ ⟨ A ⇒ A₁ `⊎ A₂ ⟩) (M′ ⟨ B ⇒ (A₁ ⇒ ⨆ bc) ⟩) (N′ ⟨ C ⇒ (A₂ ⇒ ⨆ bc) ⟩)
    , (⊢case (⊢⟨⟩ ⊢L′ {match⊎-~ a12}) (⊢⟨⟩ ⊢M′ {c1}) (⊢⟨⟩ ⊢N′ {c2})) ⟩
compile {Γ} {A} {M} (⊢⦂ ⊢M) = {!!}
```
