```
{-# OPTIONS --rewriting #-}
module lecture-notes-Substitution where
```

# Imports

```
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
                         renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂) renaming (subst to change)
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Need the following two imports for rewriting  
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

# Substitution theorems

    substitution : ∀{Γ}{A}{B}{C}
       (M : Γ , B , C ⊢ A) (N : Γ , B ⊢ C) (L : Γ ⊢ B)
      → M [ N ] [ L ] ≡ M 〔 L 〕 [ N [ L ] ]
    substitution {Γ}{A}{B}{C} M N L = refl

    exts-sub-cons : ∀{Γ}{Δ}{A}{B} (σ : Γ →ˢ Δ) (N : Γ , A ⊢ B) (V : Δ ⊢ A)
      → (subst (exts σ) N) [ V ] ≡ subst (V • σ) N
    exts-sub-cons {Γ} σ N V = refl

The proofs of these theorems are technical and can be lengthy.
Here we use the σ-algebra of Abadi et al. (Explicit Substitutions, JFP 1991)
and Agda's rewriting option to make the proofs more succinct.

The σ-algebra includes the following equations.

    (sub-head)  (M • σ) Z     ≡ M
    (sub-tail)  ↑ ⨟ (M • σ)    ≡ σ
    (sub-η)     (σ Z) • (↑ ⨟ σ) ≡ σ
    (Z-shift)   (` Z) • ↑      ≡ id
    (sub-id)    subst id M      ≡ M
    (sub-sub)   subst τ (subst σ) M  ≡ subst (σ ⨟ τ) M
    (sub-id-left)  id ⨟ σ         ≡ σ
    (sub-id-right) σ ⨟ id         ≡ σ
    (sub-assoc)    (σ ⨟ τ) ⨟ θ    ≡ σ ⨟ (τ ⨟ θ)
    (sub-dist)     (M • σ) ⨟ τ    ≡ (⟪ τ ⟫ M) • (σ ⨟ τ)


# Types, contexts, and variables

```
infixr 7 _⇒_
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

infixl 5 _,_
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

infix  4 _∋_
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
```

# Renamings

A renaming maps variables from one context to another context.
Alternatively, think of a renaming as an stream of variables.

```
infixr 7 _→ʳ_
_→ʳ_ : Context → Context → Set
Γ →ʳ Δ = (∀ {A} → Γ ∋ A → Δ ∋ A)
```

The following operation adds a variable to the front of the stream,
like `cons`.

```
infixr 6 _•ʳ_
_•ʳ_ : ∀{Γ Δ A} → (Δ ∋ A) → (Γ →ʳ Δ) → ((Γ , A) →ʳ Δ)
(x •ʳ ρ) Z = x
(x •ʳ ρ) (S y) = ρ y
```

The next operation shifts every variable in the stream.

```
⇑ʳ : ∀{Γ Δ A} → (Γ →ʳ Δ) → (Γ →ʳ (Δ , A))
⇑ʳ ρ x = S (ρ x)
```

The `ext` operation moves a renaming `ρ` past one binder (such as λ).

```
ext : ∀{Γ}{Δ}{A} → (Γ →ʳ Δ) → ((Γ , A) →ʳ (Δ , A))
ext ρ = Z •ʳ ⇑ʳ ρ
```

The identity renaming.

```
idʳ : ∀{Γ} → Γ →ʳ Γ
idʳ x = x
```

The following lemma is used to prove that applying an identity substitution is the identity.
The lemma says that applying `ext` to the identity renaming is just the identity.
The theorem statement expands `ext idʳ` to `(Z •ʳ ⇑ʳ idʳ)` so that Agda will allow
this theorem as an automatic rewrite.

```
Z-•-⇑ʳ : ∀{Γ}{A}{B} → (Z •ʳ ⇑ʳ idʳ) ≡ idʳ{Γ , A}{B}
Z-•-⇑ʳ {Γ}{A}{B} = extensionality G
  where G : (x : Γ , A ∋ B) → (Z •ʳ ⇑ʳ idʳ) x ≡ idʳ x
        G Z = refl
        G (S x) = refl
{-# REWRITE Z-•-⇑ʳ #-}
```


# Terms

```
infix  4 _⊢_
data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  `zero : ∀ {Γ}
      ---------
    → Γ ⊢ `ℕ
```

# Applying a renaming to a term

```
rename : ∀ {Γ Δ A}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → Γ ⊢ A
    ------------------
  → Δ ⊢ A
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
```

# Substitutions

A substitution maps variables from one context to terms of another.
Alternatively, think of a substitution as a stream of terms.

```
infixr 7 _→ˢ_
_→ˢ_ : Context → Context → Set
Γ →ˢ Δ = (∀ {A} → Γ ∋ A → Δ ⊢ A)
```

The following operation adds a term to the front of the stream,
like `cons`.

```
infixr 6 _•_
_•_ : ∀{Γ Δ A} → (Δ ⊢ A) → (Γ →ˢ Δ) → ((Γ , A) →ˢ Δ)
(M • σ) Z = M
(M • σ) (S y) = σ y
```

The identity substitution.

```
id : ∀{Γ} → Γ →ˢ Γ
id x = ` x
```

The `↑` substitution is the stream 0, 1, 2, ...

```
↑ : ∀{Γ A} → Γ →ˢ (Γ , A)
↑ x = ` (S x)
```

The next operation shifts every term in the stream.
This operator is not part of the σ-algebra, but its use
helps in boot-strapping the proofs of the σ-algebra equations.

```
⇑ : ∀{Γ Δ A} → (Γ →ˢ Δ) → (Γ →ˢ (Δ , A))
⇑ σ x = rename S_ (σ x)
```

The `exts` operation moves a substitution `σ` past one binder (such as λ).

```
exts : ∀{Γ}{Δ}{A} → (Γ →ˢ Δ) → ((Γ , A) →ˢ (Δ , A))
exts σ = (` Z) • ⇑ σ
```

The `subst` function applies a substitution to a term.

```
subst : ∀ {Γ Δ A} (σ : Γ →ˢ Δ) → (Γ ⊢ A) → (Δ ⊢ A)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
```

We define substitution of a single term for the zero index within another term.

```
_[_] : ∀{Γ}{A}{B} → (Γ , B ⊢ A) → (Γ ⊢ B) → (Γ ⊢ A)
N [ M ] =  subst (M • id) N
```

We also define substitution of a single term for the one index within another term.

```
_〔_〕 : ∀{Γ}{A}{B}{C} → (Γ , B , C ⊢ A) → (Γ ⊢ B) → (Γ , C ⊢ A)
_〔_〕 N M = subst (exts (M • id)) N
```

The next operator is sequencing (i.e. composition of) substitutions.
We declare the operation abstract as a workaround of
Agda's restrictions on what is allowed as a rewrite.

```
abstract
  infixr 5 _⨟_
  _⨟_ : ∀{Γ₁ Γ₂ Γ₃ : Context} → (Γ₁ →ˢ Γ₂) → (Γ₂ →ˢ Γ₃) → (Γ₁ →ˢ Γ₃)
  (σ₁ ⨟ σ₂) x = subst σ₂ (σ₁ x)

  seqˢ-def : ∀{Γ₁ Γ₂ Γ₃ A} (σ₁ : Γ₁ →ˢ Γ₂) → (σ₂ : Γ₂ →ˢ Γ₃) (x : Γ₁ ∋ A)
    → (σ₁ ⨟ σ₂) x ≡ subst σ₂ (σ₁ x)
  seqˢ-def σ₁ σ₂ x = refl
{-# REWRITE seqˢ-def #-}
```

We can convert a renaming to a substitution as follows.

```
ren : ∀{Γ}{Δ} → (Γ →ʳ Δ) → (Γ →ˢ Δ)
ren ρ x = ` ρ x
```

# Proving the σ-algebra equations

I chose the order in which to prove the equations carefully so that the
we can use REWRITE with the earlier equations to automate the
equational reasoning in the later proofs.

We start with `sub-dist`.

```
sub-dist : ∀{Γ}{Δ}{Ψ}{A}{B} (M : Δ ⊢ A) (σ : Γ →ˢ Δ)  (τ : Δ →ˢ Ψ) 
   → ((M • σ) ⨟ τ){B} ≡ (subst τ M) • (σ ⨟ τ)
sub-dist{Γ}{Δ}{Ψ}{A}{B} M σ τ = extensionality Goal
  where Goal : (x : Γ , A ∋ B) →
           ((M • σ) ⨟ τ){B} x ≡ ((subst τ M) • (σ ⨟ τ)) x
        Goal Z = refl
        Goal (S x) = refl
{-# REWRITE sub-dist #-}
```

The next equation we aim to prove is `sub-sub`. But the proof requires a whole bunch of lemmas.
The first lemmas lifts a renaming out from under an `exts`.

```
exts-ren : ∀{Γ}{Δ}{A}{B} (ρ : Γ →ʳ Δ)
  → ((` Z) • ⇑ (ren ρ)){B} ≡ ren (Z •ʳ ⇑ʳ ρ)
exts-ren{Γ}{Δ}{A}{B} ρ = extensionality Goal
  where
  Goal : (x : Γ , A ∋ B) → ((` Z) • ⇑ (ren ρ)){B} x ≡ ren (Z •ʳ ⇑ʳ ρ) x
  Goal Z = refl
  Goal (S x) = refl
{-# REWRITE exts-ren #-}
```

The above lemma is exactly what we need to prove that applying a renaming
is the same as converting the renaming to a substitution, and applying that.

```
rename-subst-ren : ∀{Γ}{Δ}{A} (ρ : Γ →ʳ Δ)(M : Γ ⊢ A)
   → rename ρ M ≡ subst (ren ρ) M
rename-subst-ren ρ (` x) = refl
rename-subst-ren ρ (ƛ N) = cong ƛ_ (rename-subst-ren (ext ρ) N)
rename-subst-ren ρ (L · M) = cong₂ _·_ (rename-subst-ren ρ L) (rename-subst-ren ρ M)
rename-subst-ren ρ `zero = refl
{-# REWRITE rename-subst-ren #-}
```

The next lemma says that `exts` distributes with sequencing
a renaming followed by a substitution.

```
ext-ren-sub : ∀{Γ}{Δ}{Ψ}{A}{B} (ρ : Γ →ʳ Δ) (τ : Δ →ˢ Ψ)
  → (exts{A = B} (ren ρ)) ⨟ (exts τ) ≡ (exts (ren ρ ⨟ τ)) {A}
ext-ren-sub{Γ}{Δ}{Ψ}{A}{B} ρ τ = extensionality G
  where G : ∀ (x : Γ , B ∋ A) → ((exts (ren ρ)) ⨟ (exts τ)) x ≡ (exts (ren ρ ⨟ τ)) x
        G Z = refl
        G (S x) = refl
{-# REWRITE ext-ren-sub #-}
```

Applying a renaming and then a subsutution is equivalent to applying their composition.
The proof relies on `ext-ren-sub`.

```
ren-sub : ∀{Γ}{Δ}{Ψ}{A} (ρ : Γ →ʳ Δ) (τ : Δ →ˢ Ψ) (M : Γ ⊢ A)
  → subst τ (subst (ren ρ) M) ≡ subst (ren ρ ⨟ τ) M
ren-sub ρ τ (` x) = refl
ren-sub ρ τ (ƛ N) = cong ƛ_ (ren-sub (ext ρ) (exts τ) N)
ren-sub ρ τ (L · M) = cong₂ _·_ (ren-sub ρ τ L) (ren-sub ρ τ M)
ren-sub ρ τ `zero = refl
{-# REWRITE ren-sub #-}
```

The other direction is also true, that is, first applying a substitution
and then a renaming is equivalent to applying their composition.
This proof relies on `rename-subst-ren` and `ren-sub`.

```
sub-ren : ∀{Γ}{Δ}{Ψ}{A} (σ : Γ →ˢ Δ) (ρ : Δ →ʳ Ψ) (M : Γ ⊢ A)
  → subst (ren ρ) (subst σ M) ≡ subst (σ ⨟ ren ρ) M
sub-ren σ ρ (` x) = refl
sub-ren σ ρ (ƛ N) = cong ƛ_ (sub-ren (exts σ) (ext ρ) N)
sub-ren σ ρ (L · M) = cong₂ _·_ (sub-ren σ ρ L) (sub-ren σ ρ M)
sub-ren σ ρ `zero = refl
{-# REWRITE sub-ren #-}
```

We finally come to the proof of `sub-sub`, which states that applying
one substitution after another is equivalent to applying their composition.
The proof relies on `sub-ren`.

```
sub-sub : ∀{Γ}{Δ}{Ψ}{A} (σ : Γ →ˢ Δ) (τ : Δ →ˢ Ψ) (M : Γ ⊢ A)
  → subst τ (subst σ M) ≡ subst (σ ⨟ τ) M
sub-sub σ τ (` x) = refl
sub-sub σ τ (ƛ N) = cong ƛ_ (sub-sub (exts σ) (exts τ) N)
sub-sub σ τ (L · M) = cong₂ _·_ (sub-sub σ τ L) (sub-sub σ τ M)
sub-sub σ τ `zero = refl
{-# REWRITE sub-sub #-}
```

The rest of the equations are relatively easy.

Applying an identity substitution is the identity.

```
sub-id : ∀ {Γ}{A} (M : Γ ⊢ A)
  → subst id M ≡ M
sub-id (` x) = refl
sub-id {Γ}{A ⇒ B} (ƛ N) = cong ƛ_ (sub-id N)
sub-id (L · M) = cong₂ _·_ (sub-id L) (sub-id M)
sub-id `zero = refl
{-# REWRITE sub-id #-}
```

The equations we have already proved are enough to
prove the `sub-head` and `sub-tail` equations.

```
sub-head : ∀{Γ Δ}{A} (M : Δ ⊢ A) (σ : Γ →ˢ Δ)
  → (M • σ) Z ≡ M
sub-head M σ = refl

sub-tail : ∀{Γ Δ}{A B} (M : Δ ⊢ A) (σ : Γ →ˢ Δ)
  → (↑ ⨟ (M • σ)) ≡ σ{B}
sub-tail y σ = refl
```

To prove `sub-η` we just do a case analysis on
the zero and non-zero cases.

```
sub-η : ∀{Γ}{Δ}{A}{B} (σ : (Γ , A) →ˢ Δ)
  → (σ Z) • (↑ ⨟ σ) ≡ σ{B}
sub-η{Γ}{Δ}{A}{B} σ = extensionality G
  where G : (x : Γ , A ∋ B) → (σ Z • (↑ ⨟ σ)) x ≡ σ x
        G Z = refl
        G (S x) = refl
```

The equations we have already proved are
enough to prove the next four equations.

```
Z-shift : ∀{Γ}{A}{B} → (` Z • ↑) ≡ id{Γ , A}{B}
Z-shift {Γ}{A}{B} = refl

sub-id-left : ∀{Γ Δ}{A} → (σ : Γ →ˢ Δ)
  → id ⨟ σ ≡ σ{A}
sub-id-left σ = refl

sub-id-right : ∀{Γ Δ}{A} → (σ : Γ →ˢ Δ)
  → σ ⨟ id ≡ σ{A}
sub-id-right σ = refl

sub-assoc : ∀{Γ}{Δ}{Ψ}{Θ}{A} (σ : Γ →ˢ Δ) (τ : Δ →ˢ Ψ) (θ : Ψ →ˢ Θ)
  → (σ ⨟ τ) ⨟ θ ≡ (σ ⨟ τ ⨟ θ){A}
sub-assoc σ τ θ = refl
```

The extra operator `⇑ σ` that we used to boot-strap the
proof is equivalent to `σ ⨟ ↑`.

```
⇑-↑-seq : ∀ {Γ}{Δ}{A}{B} (σ : Γ →ˢ Δ)
  → (⇑{A = A} σ) ≡ (σ ⨟ ↑){B}
⇑-↑-seq σ = refl
```

We now come to the main event, the proofs of the `substitution` and `exts-sub-cons` theorems.
Both are automatic consequences of equations that we've already proved.

```
substitution : ∀{Γ}{A}{B}{C}
   (M : Γ , B , C ⊢ A) (N : Γ , B ⊢ C) (L : Γ ⊢ B)
  → M [ N ] [ L ] ≡ M 〔 L 〕 [ N [ L ] ]
substitution {Γ}{A}{B}{C} M N L = refl

exts-sub-cons : ∀{Γ}{Δ}{A}{B} (σ : Γ →ˢ Δ) (N : Γ , A ⊢ B) (V : Δ ⊢ A)
  → (subst (exts σ) N) [ V ] ≡ subst (V • σ) N
exts-sub-cons {Γ} σ N V = refl
```
