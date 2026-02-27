```
module lecture-notes-Bisimulation where

open import Function using (case_of_)


infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  9 `_
infix  5 ƛ_
infixl 7 _·_

data Type : Set where
  `ℕ     : Type
  _⇒_   : Type → Type → Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B

data _⊢_ : Context → Type → Set where

  `zero : ∀ {Γ}
      ------
    → Γ ⊢ `ℕ

  `_ : ∀ {Γ A}
    → Γ ∋ A
      ---------
    → Γ ⊢ A

  ƛ_  :  ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------------
    → Γ ⊢ B

  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ---------------
    → Γ ⊢ B

ext : ∀ {Γ Δ}
  → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
    ------------------------------------------
  → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (`zero)        =  `zero
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`let M N)     =  `let (rename ρ M) (rename (ext ρ) N)

exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ⊢ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
subst σ (`zero)        =  `zero
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)

_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x

data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)


infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  -- functions

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
    → M —→ M′
      ---------------------
    → `let M N —→ `let M′ N

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
    → Value V
      ------------------------------
    → (ƛ N) · V —→ N [ V ]

  β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
    → Value V
      ------------------------------
    → `let V N —→ N [ V ]

infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

data _~_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where

  ~zero : ∀ {Γ}
     ------------------
   → `zero ~ `zero {Γ}

  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ---------------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ----------------------
    → `let M N ~ (ƛ N†) · M†
```
Simulation commutes with values: if M ~ M† and M is a value then M† is also a value
```
~val : ∀ {Γ A} {V V† : Γ ⊢ A}
  → V ~ V†
  → Value V
    ------------
  → Value V†
~val ~zero   V-zero = V-zero
~val (~ƛ ~N) V-ƛ    = V-ƛ
```
The other direction is also true:
```
~val⁻¹ : ∀ {Γ A} {V V† : Γ ⊢ A}
  → V ~ V†
  → Value V†
    ------------
  → Value V
~val⁻¹ ~zero   V-zero = V-zero
~val⁻¹ (~ƛ ~N) V-ƛ    = V-ƛ
```
Simulation commutes with renaming: if ρ maps any judgment Γ ∋ A to a judgment Δ ∋ A,
and if M ~ M† then rename ρ M ~ rename ρ M†
```
~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
    ----------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
~rename ρ ~zero         =  ~zero
~rename ρ (~`)          =  ~`
~rename ρ (~ƛ ~N)       =  ~ƛ (~rename (ext ρ) ~N)
~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)
~rename ρ (~let ~M ~N)  =  ~let (~rename ρ ~M) (~rename (ext ρ) ~N)
```
Simulation commutes with substitution: If σ and σ† both map any judgment Γ ∋ A to
a judgment Δ ⊢ A, such that for every x in Γ ∋ A we have σ x ~ σ† x,
and if M ~ M†, then subst σ M ~ subst σ† M†
```
~exts : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    --------------------------------------------------
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~ exts σ† x)
~exts ~σ Z      =  ~`
~exts ~σ (S x)  =  ~rename S_ (~σ x)

~subst : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    ---------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → subst σ M ~ subst σ† M†)
~subst ~σ ~zero         =  ~zero
~subst ~σ (~` {x = x})  =  ~σ x
~subst ~σ (~ƛ ~N)       =  ~ƛ (~subst (~exts ~σ) ~N)
~subst ~σ (~L ~· ~M)    =  (~subst ~σ ~L) ~· (~subst ~σ ~M)
~subst ~σ (~let ~M ~N)  =  ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)

~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
  → N ~ N†
  → M ~ M†
    -----------------------
  → (N [ M ]) ~ (N† [ M† ])
~sub {Γ} {A} {B} ~N ~M = ~subst {Γ , B} {Γ} ~σ {A} ~N
  where
  ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
  ~σ Z      =  ~M
  ~σ (S x)  =  ~`

data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

  leg : ∀ {N† : Γ ⊢ A}
    → N ~ N†
    → M† —→ N†
      --------
    → Leg M† N

sim : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ M†
  → M —→ N
    ---------
  → Leg  M† N
sim ~`              ()
sim (~ƛ ~N)         ()
sim (~L ~· ~M)      (ξ-·₁ L—→)
  with sim ~L L—→
...  | leg ~L′ L†—→                 =  leg (~L′ ~· ~M)   (ξ-·₁ L†—→)
sim (~V ~· ~M)      (ξ-·₂ VV M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~V ~· ~M′)   (ξ-·₂ (~val ~V VV) M†—→)
sim ((~ƛ ~N) ~· ~V) (β-ƛ VV)        =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
sim (~let ~M ~N)    (ξ-let M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~let ~M′ ~N) (ξ-·₂ V-ƛ M†—→)
sim (~let ~V ~N)    (β-let VV)      =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))

data Leg⁻¹ {Γ A} (M N† : Γ ⊢ A) : Set where

  leg : ∀ {N : Γ ⊢ A}
    → N ~ N†
    → M —→ N
      --------
    → Leg⁻¹ M N†

sim⁻¹ : ∀ {Γ A} {M M† N† : Γ ⊢ A}
  → M ~ M†
  → M† —→ N†
    ---------------
  → Leg⁻¹ M N†
sim⁻¹ ~` ()
sim⁻¹ (~ƛ _) ()
sim⁻¹ (L~L† ~· M~M†) (ξ-·₁ L†→L†′) =
  case sim⁻¹ L~L† L†→L†′ of λ where
  (leg L′~L†′ L→L′) → leg (L′~L†′ ~· M~M†) (ξ-·₁ L→L′)
sim⁻¹ (L~L† ~· M~M†) (ξ-·₂ vL† M†→M†′) =
  case sim⁻¹ M~M† M†→M†′ of λ where
  (leg M′~M†′ M→M′) → leg (L~L† ~· M′~M†′) (ξ-·₂ (~val⁻¹ L~L† vL†) M→M′)
sim⁻¹ ((~ƛ N~N†) ~· M~M†) (β-ƛ vM†) =
  leg (~sub N~N† M~M†) (β-ƛ (~val⁻¹ M~M† vM†))
sim⁻¹ (~let M~M† N~N†) (ξ-·₂ vλN† M†→M†′) =
  case sim⁻¹ M~M† M†→M†′ of λ where
  (leg M′~M†′ M→M′) → leg (~let M′~M†′ N~N†) (ξ-let M→M′)
sim⁻¹ (~let M~M† N~N†) (β-ƛ vM†) =
  leg (~sub N~N† M~M†) (β-let (~val⁻¹ M~M† vM†))
```
