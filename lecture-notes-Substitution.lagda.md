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
Here we use the σ-calculus of Abadi et al. (Explicit Substitutions, JFP 1991)
and Agda's rewriting option to make the proofs much more succinct.

Think of a substitution σ as a stream of terms.

The σ-calculus consists of the following operations on substitutions.

    id           The stream:  0, 1, 2, 3, ...
    ↑            The stream:  1, 2, 3, 4, ...
    (M • σ)      Cons a term M onto the front of the stream σ
    σ ⨟ τ        The stream:  subst τ (σ 0), subst τ (σ 1), subst τ (σ 2), ...

The σ-calculus includes the following equations.

    (sub-head)             (M • σ) Z ≡ M
    (sub-tail)           ↑ ⨟ (M • σ) ≡ σ
    (sub-η)          (σ Z) • (↑ ⨟ σ) ≡ σ
    (Z-shift)              (` Z) • ↑ ≡ id
    (sub-id)             subst id M  ≡ M
    (sub-sub)   subst τ (subst σ M)  ≡ subst (σ ⨟ τ) M
    (sub-id-left)             id ⨟ σ ≡ σ
    (sub-id-right)            σ ⨟ id ≡ σ
    (sub-assoc)          (σ ⨟ τ) ⨟ θ ≡ σ ⨟ (τ ⨟ θ)
    (sub-dist)           (M • σ) ⨟ τ ≡ (⟪ τ ⟫ M) • (σ ⨟ τ)


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

The above definition of `ext` is equivalent to the one from PLFA.

```
old-ext : ∀ {Γ Δ}{A}
  → (Γ →ʳ Δ)
  → (Γ , A) →ʳ (Δ , A)
old-ext ρ Z      =  Z
old-ext ρ (S x)  =  S (ρ x)
```

```
ext-equiv : ∀ {Γ Δ}{A}{B}(ρ : Γ →ʳ Δ) (x : Γ , A ∋ B) → ext ρ x ≡ old-ext ρ x
ext-equiv ρ Z = refl
ext-equiv ρ (S x) = refl
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


# Terms (Same as in the DeBruijn chapter)

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

# Applying a renaming to a term (same as in DeBruin)

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
This operator is not part of the σ-calculus, but its use
helps in boot-strapping the proofs of the σ-calculus equations.

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

# Proving the σ-calculus equations

I chose the order in which to prove the equations carefully so that the
we can use REWRITE with the earlier equations to automate the
equational reasoning in the later proofs.

The equation (sub-head) follows immediately from the definition of •.
We don't need to register (sub-head) as a REWRITE because it is already automatic.

```
sub-head : ∀{Γ Δ}{A} (M : Δ ⊢ A) (σ : Γ →ˢ Δ)
  → (M • σ) Z ≡ M
sub-head M σ = refl
```

Likewise, `sub-tail` follows from the definition of the operators ⨟, ↑, and •.

```
sub-tail : ∀{Γ Δ}{A B} (M : Δ ⊢ A) (σ : Γ →ˢ Δ)
  → (↑ ⨟ (M • σ)) ≡ σ{B}
sub-tail M σ =
  -- short version: refl
  -- long version:
  begin
    (↑ ⨟ (M • σ)) ≡⟨⟩
    (λ x → subst (M • σ) (↑ x)) ≡⟨⟩
    (λ x → subst (M • σ) (` (S x))) ≡⟨⟩
    (λ x → (M • σ) (S x)) ≡⟨⟩
    (λ x → σ x) ≡⟨⟩
    σ
  ∎
```

We start with `sub-dist`. The proof is by cases on zero and non-zero.

```
sub-dist : ∀{Γ}{Δ}{Ψ}{A}{B} (M : Δ ⊢ A) (σ : Γ →ˢ Δ)  (τ : Δ →ˢ Ψ) 
   → ((M • σ) ⨟ τ){B} ≡ (subst τ M) • (σ ⨟ τ)
sub-dist{Γ}{Δ}{Ψ}{A}{B} M σ τ = extensionality Goal
  where Goal : (x : Γ , A ∋ B) → ((M • σ) ⨟ τ){B} x ≡ ((subst τ M) • (σ ⨟ τ)) x
        Goal Z = refl
        Goal (S x′) = refl
{-# REWRITE sub-dist #-}
```

The next equation we aim to prove is `sub-sub`. But the proof requires a whole bunch of lemmas.
The first lemma commutes `exts` and `ren`. We have to expand both `exts` and `ext` for
Agda to accept this as a rewrite rule.

```
exts-ren : ∀{Γ}{Δ}{A}{B} (ρ : Γ →ʳ Δ)
  → ((` Z) • ⇑ (ren ρ)){B} ≡ ren (Z •ʳ ⇑ʳ ρ)  -- exts (ren ρ) ≡ ren (ext ρ)
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
rename-subst-ren ρ (ƛ N) =
  -- short version: cong ƛ_ (rename-subst-ren (ext ρ) N)
  -- human readable version:
  begin
    rename ρ (ƛ N)                   ≡⟨⟩
    ƛ (rename (ext ρ) N)             ≡⟨ cong ƛ_ IH ⟩
    ƛ (subst (ren (ext ρ)) N)        ≡⟨⟩ -- exts-ren
    ƛ (subst (exts (ren ρ)) N)       ≡⟨⟩
    subst (ren ρ) (ƛ N)
  ∎
  where IH : rename (ext ρ) N ≡ subst (ren (ext ρ)) N
        IH = (rename-subst-ren (ext ρ) N)
rename-subst-ren ρ (L · M) = cong₂ _·_ (rename-subst-ren ρ L) (rename-subst-ren ρ M)
rename-subst-ren ρ `zero = refl
{-# REWRITE rename-subst-ren #-}
```

The extra operator `⇑ σ` that we use to boot-strap the
proof is equivalent to `σ ⨟ ↑`.

```
⇑-↑-seq : ∀ {Γ}{Δ}{A}{B} (σ : Γ →ˢ Δ)
  → (⇑{A = A} σ) ≡ (σ ⨟ ↑){B}
⇑-↑-seq{Γ}{Δ}{A}{B} σ =
  -- short version: refl
  -- human readable version:
  begin
    ⇑ σ                           ≡⟨⟩ -- def ⇑ 
    (λ x → rename S_ (σ x))       ≡⟨⟩ -- rename-subst-ren
    (λ x → subst (ren S_) (σ x))  ≡⟨⟩ -- def ⨟ 
    (σ ⨟ ↑)
  ∎
```

The next lemma says that `exts` distributes with sequencing
a renaming followed by a substitution.

```
ext-ren-sub : ∀{Γ}{Δ}{Ψ}{A}{B} (ρ : Γ →ʳ Δ) (τ : Δ →ˢ Ψ)
  → exts (ren ρ) ⨟ exts τ ≡ exts (ren ρ ⨟ τ) {A}
ext-ren-sub{Γ}{Δ}{Ψ}{A}{B} ρ τ = extensionality G
  where G : ∀ (x : Γ , B ∋ A) → (exts (ren ρ) ⨟ exts τ) x ≡ exts (ren ρ ⨟ τ) x
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
ren-sub ρ τ (ƛ N) =
  -- short version: cong ƛ_ (ren-sub (ext ρ) (exts τ) N)
  -- human readable version:
  begin
    subst τ (subst (ren ρ) (ƛ N))             ≡⟨⟩ -- def subst
    ƛ subst (exts τ) (subst (exts (ren ρ)) N) ≡⟨⟩ -- exts-ren
    ƛ subst (exts τ) (subst (ren (ext ρ)) N)  ≡⟨ cong ƛ_ IH ⟩
    ƛ subst (ren (ext ρ) ⨟ exts τ) N          ≡⟨⟩ -- exts-ren
    ƛ subst (exts (ren ρ) ⨟ exts τ) N         ≡⟨⟩ -- ext-ren-sub 
    ƛ subst (exts (ren ρ ⨟ τ)) N              ≡⟨⟩
    subst (ren ρ ⨟ τ) (ƛ N)
  ∎
  where IH : subst (exts τ) (subst (ren (ext ρ)) N) ≡ subst (ren (ext ρ) ⨟ (exts τ)) N
        IH = (ren-sub (ext ρ) (exts τ) N)
ren-sub ρ τ (L · M) = cong₂ _·_ (ren-sub ρ τ L) (ren-sub ρ τ M)
ren-sub ρ τ `zero = refl
{-# REWRITE ren-sub #-}
```

The other direction is also true, that is, first applying a substitution
and then a renaming is equivalent to applying their composition.
The hard part of this proof relies on `rename-subst-ren`, `ren-sub`, and `exts-ren`.

```
sub-ren : ∀{Γ}{Δ}{Ψ}{A} (σ : Γ →ˢ Δ) (ρ : Δ →ʳ Ψ) (M : Γ ⊢ A)
  → subst (ren ρ) (subst σ M) ≡ subst (σ ⨟ ren ρ) M
sub-ren σ ρ (` x) = refl
sub-ren{A = A} σ ρ (ƛ N) =
  -- short version: cong ƛ_ (sub-ren (exts σ) (ext ρ) N)
  -- human readable version:
  let IH : subst (ren (ext ρ)) (subst (exts σ) N) ≡ subst ((exts σ) ⨟ ren (ext ρ)) N
      IH = (sub-ren (exts σ) (ext ρ) N) in
  begin
    subst (ren ρ) (subst σ (ƛ N))                   ≡⟨⟩ -- def subst
    ƛ subst (exts (ren ρ)) (subst (exts σ) N)       ≡⟨ cong ƛ_ IH ⟩
    ƛ subst ((exts σ) ⨟ ren (ext ρ)) N              ≡⟨⟩ -- hard part! (many steps)
    ƛ subst (exts (σ ⨟ ren ρ)) N                    ≡⟨⟩ -- def subst
    subst (σ ⨟ ren ρ) (ƛ N)
  ∎
sub-ren σ ρ (L · M) = cong₂ _·_ (sub-ren σ ρ L) (sub-ren σ ρ M)
sub-ren σ ρ `zero = refl
{-# REWRITE sub-ren #-}
```

We finally come to the proof of `sub-sub`, which states that applying
one substitution after another is equivalent to applying their composition.
The proof relies on `sub-ren` and other lemmas.

```
sub-sub : ∀{Γ}{Δ}{Ψ}{A} (σ : Γ →ˢ Δ) (τ : Δ →ˢ Ψ) (M : Γ ⊢ A)
  → subst τ (subst σ M) ≡ subst (σ ⨟ τ) M
sub-sub σ τ (` x) = refl
sub-sub σ τ (ƛ N) =
  -- short version: cong ƛ_ (sub-sub (exts σ) (exts τ) N)
  -- longer version:
  let IH : subst (exts τ) (subst (exts σ) N) ≡ subst (exts σ ⨟ exts τ) N
      IH = sub-sub (exts σ) (exts τ) N in
  begin
    subst τ (subst σ (ƛ N))                      ≡⟨⟩ -- def subst
    ƛ subst (exts τ) (subst (exts σ) N)          ≡⟨ cong ƛ_ IH ⟩
    ƛ subst (exts σ ⨟ exts τ) N                  ≡⟨⟩ -- hard part! (many steps)
    ƛ subst (exts (σ ⨟ τ)) N                     ≡⟨⟩ -- def subst
    subst (σ ⨟ τ) (ƛ N)
  ∎
sub-sub σ τ (L · M) = cong₂ _·_ (sub-sub σ τ L) (sub-sub σ τ M)
sub-sub σ τ `zero = refl
{-# REWRITE sub-sub #-}
```

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

To prove `sub-η` we do cases for zero and non-zero.

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


**Exercise:** write down detailed proofs of the hard parts of `sub-ren` and `sub-sub`:

    (exts σ) ⨟ ren (ext ρ)  ≡  exts (σ ⨟ ren ρ)

           exts σ ⨟ exts τ  ≡ exts (σ ⨟ τ)

