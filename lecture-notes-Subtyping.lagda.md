```
{-# OPTIONS --rewriting #-}

module lecture-notes-Subtyping where
```

## Imports

```
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Vec
  using (Vec; toList; []; _∷_; lookup)
open import Data.Fin using (Fin; zero; suc; reduce≥)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Data.Vec.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
   using (≤-refl; ≤-pred; m+n≤o⇒m≤o; m+n≤o⇒n≤o; n≤0⇒n≡0; ≤-step)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
   renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)

-- Need the following two imports for rewriting  
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite


postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

## Review of textbook (TAPL) definition of records and subtyping

Syntax

    t ::= ...               terms:
          {lᵢ=tᵢ i∈1..n }    record
          t.l                 projection

    v ::= ...               values:
          {lᵢ= vᵢ i∈1..n }    record value

    T ::= ...               types:
          {lᵢ :Tᵢ i∈1..n }    type of records 

Reduction

    {lᵢ=vᵢ i∈1..n }.lⱼ ⟶ vⱼ

    t ⟶ t′
    ------------
    t.l ⟶ t′.l
    
    tⱼ ⟶ t′ⱼ
    ---------------------------------------------
    {lᵢ=vᵢ i∈1..j−1 ,lⱼ =tⱼ, lk=tk k∈j+1..n }
    ⟶ {lᵢ=vᵢ i∈1..j−1 ,lⱼ =t′ⱼ, lk=tk k∈j+1..n }

Subtyping rules

    ------ (S-Refl)
    S <: S

    S <: U   U <: T
    --------------- (S-Trans)
    S <: T

    -------- (S-Top)
    S <: Top

    T₁ <: S₁   S₂ <: T₂
    ------------------- (S-Arrow) 
    S₁ → S₂ <: T₁ → T₂

    --------------------------------------
    {li :Ti i∈1..n+k } <: {li :Ti i∈1..n } (S-RcdWidth)

    ∀ i. Si <: Ti
    ------------------------------------
    {li :Si i∈1..n } <: {li :Ti i∈1..n } (S-RcdDepth) 


    {kj :Sj j∈1..n } is a permutation of {li :Ti i∈1..n }
    -----------------------------------------------------
    {kj :Sj j∈1..n } <: {li :Ti i∈1..n }  (S-RcdPerm) 


Typing rules

    ...

    Γ ⊢ t : S   S <: T
    ------------------ (T-Sub)
    Γ ⊢ t : T

    ∀ i. Γ ⊢ ti : Ti
    --------------------------------------- (T-Rcd)
    Γ ⊢ {li =ti i∈1..n } : {li :Ti i∈1..n }

    Γ ⊢ t : {li : Ti i∈1..n }
    -------------------------  (T-Proj) 
    Γ ⊢ t.lj : Tj


## Properties of Record Field Names and Field Lookup

We shall represent field identifiers (aka. names) as strings.

```
Id : Set
Id = String
```

The field identifiers of a record will be stored in a sequence,
specifically Agda's `Vec` type. We define the following short-hand for
the `lookup` function that retrieve's the ith element in the sequence.

```
infix  9 _❲_❳
_❲_❳ : ∀{n}{A : Set} → Vec A n → Fin n → A
xs ❲ i ❳ = lookup xs i
```

We require that the field names of a record be distinct, which we
define as follows.

```
distinct : ∀{A : Set}{n} → Vec A n → Set
distinct [] = ⊤
distinct (x ∷ xs) = ¬ (x ∈ xs) × distinct xs
```

The following function implements decidable membership in a `Vec`.
The Agda stdlib should have this, but I couldn't find it in a short
amount of time.

[It's in Data.Vec.Membership.DecPropositional.agda -Jeremy]

```
_∈?_ : ∀{n} (x : Id) → (xs : Vec Id n) → Dec (x ∈ xs)
x ∈? [] = no λ ()
x ∈? (y ∷ xs)
    with x ≟ y
... | yes xy = yes (here xy)
... | no xy
    with x ∈? xs
... | yes x∈xs = yes (there x∈xs)
... | no x∉xs = no λ { (here a) → xy a ; (there a) → x∉xs a } 
```

The next function decides whether a vector is distinct.

```
distinct? : ∀{n} → (xs : Vec Id n) → Dec (distinct xs)
distinct? [] = yes tt
distinct? (x ∷ xs)
    with x ∈? xs
... | yes x∈xs = no λ z → proj₁ z x∈xs
... | no x∉xs
    with distinct? xs
... | yes dxs = yes ⟨ x∉xs , dxs ⟩
... | no ¬dxs = no λ x₁ → ¬dxs (proj₂ x₁)
```

This function turns an irrelevant proof that a vector is distinct into
a relevant proof.

```
distinct-rel : ∀ {n}{fs : Vec Id n} .(d : distinct fs) → distinct fs
distinct-rel {n}{fs} d
    with distinct? fs
... | yes dfs = dfs
... | no ¬dfs = ⊥-elimi (¬dfs d)
```

The result of `lookup` is a member of the sequence.

```
lookup-mem : ∀{n}{fs : Vec Id n}{j : Fin n} 
           → fs ❲ j ❳ ∈ fs
lookup-mem {.(suc _)} {x ∷ fs} {zero} = here refl
lookup-mem {.(suc _)} {x ∷ fs} {suc j} = there lookup-mem
```

For distinct vectors, indexing is injective.

```
distinct-lookup-eq : ∀ {n}{fs : Vec Id n}{i j : Fin n}
   → distinct fs
   → fs ❲ j ❳ ≡ fs ❲ i ❳
   → i ≡ j
distinct-lookup-eq {.(suc _)} {x ∷ fs} {zero} {zero} ⟨ x∉fs , dfs ⟩ lij = refl
distinct-lookup-eq {suc n} {x ∷ fs} {zero} {suc j} ⟨ x∉fs , dfs ⟩ refl =
    ⊥-elim (x∉fs lookup-mem)
distinct-lookup-eq {.(suc _)} {x ∷ fs} {suc i} {zero} ⟨ x∉fs , dfs ⟩ refl =
    ⊥-elim (x∉fs lookup-mem)
distinct-lookup-eq {suc n} {x ∷ fs} {suc i} {suc j} ⟨ x∉fs , dfs ⟩ lij =
  let IH = distinct-lookup-eq {n} {fs}{i}{j} dfs lij in
  cong suc IH
```

A vector of identifiers is a subset of another one if all the
identifiers of the first vector are also in the second one.

```
data _⊆_ : ∀{n m} → Vec Id n → Vec Id m → Set where
  subseteq : ∀ {n m} {xs : Vec Id n} {ys : Vec Id m}
           → ((i : Fin n) → Σ[ j ∈ Fin m ] xs ❲ i ❳ ≡ ys ❲ j ❳)
           → xs ⊆ ys 
```

This subset relation is reflexive.

```
⊆-refl : ∀{n}{fs : Vec Id n} → fs ⊆ fs
⊆-refl {n}{fs} = subseteq (λ i → ⟨ i , refl ⟩)
```

The subset relation is also transitive.

```
⊆-trans : ∀{l n m}{ns  : Vec Id n}{ms  : Vec Id m}{ls  : Vec Id l}
        → ns ⊆ ms   →    ms ⊆ ls
        → ns ⊆ ls
⊆-trans {l}{n}{m}{ns}{ms}{ls} (subseteq a) (subseteq b) = subseteq G
    where
    G : (i : Fin n) →  Σ[ j ∈ Fin l ] ns ❲ i ❳ ≡ ls ❲ j ❳
    G i
        with a i
    ... | ⟨ j , lk1 ⟩
        with b j
    ... | ⟨ k , lk2 ⟩
        rewrite lk1 | lk2 = ⟨ k , refl ⟩
```

If one vector `ns` is a subset of another `ms`, then for any element
`ns ❲ i ❳`, there is an equal element in `ms` at some index.

```
lookup-⊆ : ∀{n m : ℕ}{ns : Vec Id n}{ms : Vec Id m}{i : Fin n}
   → ns ⊆ ms
   → Σ[ k ∈ Fin m ] ns ❲ i ❳ ≡ ms ❲ k ❳
lookup-⊆ {suc n} {m} {x ∷ ns} {ms} {i} (subseteq x₁) = x₁ i
```


## Syntax

```
infix  4 _⊢_⦂_
infixl 5 _,_

infixr 7 _⇒_
infix 6 _<:_

infix  5 λ:_⇒_
infixl 7 _·_
infixr 9 _#_

infix 4 _—→_
```


## Types

A record type is usually written

    { l₁ : A₁, l₂ : A₂, ..., lᵤ : Aᵤ }

so a natural representation would be a list of label-type pairs.
However, we find it more convenient to represent record types as a
pair of lists, one of labels and one of types:

    l₁, l₂, ..., lᵤ
    A₁, A₂, ..., Aᵤ

We represent these fixed-length lists using Agda's `Vec` type.

```
data Type : Set where
  `𝔹    : Type
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Record : (n : ℕ)(ls : Vec Id n)(As : Vec Type n) → .{d : distinct ls} → Type 
```

In the above, we used `distinct` on the field names of the record.


## Subtyping

The following definition of subtyping closely follows
the algorithmic subtyping rules in Chapter 16 of
_Types and Programming Languages_ (TAPL) by Benjamin Pierce.

```
data _<:_ : Type → Type → Set where
  <:-bool : `𝔹 <: `𝔹

  <:-nat : `ℕ <: `ℕ

  <:-fun : ∀{A B C D}
    → C <: A  → B <: D
      ----------------
    → A ⇒ B <: C ⇒ D

  <:-rcd :  ∀{m}{ks : Vec Id m}{Ss : Vec Type m}.{d1 : distinct ks}
             {n}{ls : Vec Id n}{Ts : Vec Type n}.{d2 : distinct ls}
    → ls ⊆ ks
    → (∀{i : Fin n}{j : Fin m} → ks ❲ j ❳ ≡ ls ❲ i ❳
                               → Ss ❲ j ❳ <: Ts ❲ i ❳)
      ------------------------------------------------------
    → Record m ks Ss {d1} <: Record n ls Ts {d2}
```

The first premise of the record subtyping rule (`<:-rcd`) expresses
_width subtyping_ by requiring that all the labels in `ls` are also in
`ks`. So it allows the hiding of fields when going from a subtype to a
supertype.

The second premise of the record subtyping rule (`<:-rcd`) expresses
_depth subtyping_, that is, it allows the types of the fields to
change according to subtyping. The following is an abbreviation for
this premise.

```
_⦂_<:_⦂_ : ∀ {m n} → Vec Id m → Vec Type m → Vec Id n → Vec Type n → Set
_⦂_<:_⦂_ {m}{n} ks Ss ls Ts = (∀{i : Fin n}{j : Fin m}
    → ks ❲ j ❳ ≡ ls ❲ i ❳  →  Ss ❲ j ❳ <: Ts ❲ i ❳)
```

## Subtyping is reflexive

The proof that subtyping is reflexive does not go by induction on the
type because of the `<:-rcd` rule. We instead use induction on the
size of the type. So we first define size of a type, and the size of a
vector of types, as follows.

```
ty-size : (A : Type) → ℕ
vec-ty-size : ∀ {n : ℕ} → (As : Vec Type n) → ℕ

ty-size `𝔹 = 1
ty-size `ℕ = 1
ty-size (A ⇒ B) = suc (ty-size A + ty-size B)
ty-size (Record n fs As) = suc (vec-ty-size As)

vec-ty-size {n} [] = 0
vec-ty-size {n} (x ∷ xs) = ty-size x + vec-ty-size xs
```

The size of a type is always positive.

```
ty-size-pos : ∀ {A} → 0 < ty-size A
ty-size-pos {`𝔹} = s≤s z≤n
ty-size-pos {`ℕ} = s≤s z≤n
ty-size-pos {A ⇒ B} = s≤s z≤n
ty-size-pos {Record n fs As} = s≤s z≤n
```

If a vector of types is smaller than `n`, then so is any type in the vector.

```
lookup-vec-ty-size : ∀{n}{k} {As : Vec Type k} {j}
   → vec-ty-size As ≤ n
   → ty-size (As ❲ j ❳) ≤ n
lookup-vec-ty-size {n} {suc k} {A ∷ As} {zero} As≤n =
    m+n≤o⇒m≤o (ty-size A) As≤n
lookup-vec-ty-size {n} {suc k}{A ∷ As} {suc j} As≤n =
    lookup-vec-ty-size {n} {k} {As} {j} (m+n≤o⇒n≤o (ty-size A) As≤n)
```

Here is the proof of reflexivity, by induction on the size of the type.
(Unfortunately, induction directly on type A does not work because,
in the case for Record, Agda's termination checker does not understand
that `lookup As i` is a part of `As`.)

```
<:-refl-aux : ∀{n}{A}{m : ty-size A ≤ n} → A <: A
<:-refl-aux {0}{A}{m}
    with ty-size-pos {A}
... | pos rewrite n≤0⇒n≡0 m
    with pos
... | ()    
<:-refl-aux {suc n}{`𝔹}{m} = <:-bool
<:-refl-aux {suc n}{`ℕ}{m} = <:-nat
<:-refl-aux {suc n}{A ⇒ B}{m} =
  let a = ≤-pred m in
  <:-fun (<:-refl-aux{n}{A}{m+n≤o⇒m≤o (ty-size A) a })
         (<:-refl-aux{n}{B}{m+n≤o⇒n≤o (ty-size A) a})
<:-refl-aux {suc n}{Record k fs As {d}}{m} = <:-rcd {d1 = d}{d2 = d} ⊆-refl G
    where
    G : ∀ {i j : Fin k} →
          fs ❲ j ❳ ≡ fs ❲ i ❳ → As ❲ j ❳ <: As ❲ i ❳
    G {i}{j} lij rewrite distinct-lookup-eq (distinct-rel d) lij =
        let Asⱼ≤n = lookup-vec-ty-size {n}{k}{As}{j} (≤-pred m) in 
        <:-refl-aux {n}{lookup As j}{Asⱼ≤n}
```

This corollary packages up reflexivity for ease of use.

```
<:-refl : ∀{A} → A <: A
<:-refl {A} = <:-refl-aux {ty-size A}{A}{≤-refl}
```

## Subtyping is transitive

The proof of transitivity is straightforward, given that we've
already proved the two lemmas needed in the case for `<:-rcd`:
`⊆-trans` and `lookup-⊆`.

```
<:-trans : ∀{A B C}
    → A <: B   →   B <: C
      -------------------
    → A <: C
<:-trans {.`𝔹} {`𝔹} {.`𝔹} <:-bool <:-bool = <:-bool
<:-trans {.`ℕ} {`ℕ} {.`ℕ} <:-nat <:-nat = <:-nat
<:-trans {A₁ ⇒ A₂} {B₁ ⇒ B₂} {C₁ ⇒ C₂} (<:-fun A<:B A<:B₁) (<:-fun B<:C B<:C₁) =
    <:-fun (<:-trans B<:C A<:B) (<:-trans A<:B₁ B<:C₁)
<:-trans {Record l ls As {d1} } {Record m ms Bs {d2} } {Record n ns Cs {d3} }
    (<:-rcd ms⊆ls As<:Bs) (<:-rcd ns⊆ms Bs<:Cs) =
    <:-rcd (⊆-trans ns⊆ms ms⊆ls) G
    where
    G : {i : Fin n} {j : Fin l} →
      lookup ls j ≡ lookup ns i → lookup As j <: lookup Cs i
    G {i}{j} lij
        with lookup-⊆ {i = i} ns⊆ms 
    ... | ⟨ k , lik ⟩
        with lookup-⊆ {i = k} ms⊆ls
    ... | ⟨ j' , lkj' ⟩ rewrite sym lkj' | lij | sym lik  =
        let ab = As<:Bs {k}{j} (trans lij lik) in
        let bc = Bs<:Cs {i}{k} (sym lik) in
        <:-trans ab bc
```

## Primitives

We use Agda values as primitive constants. We include natural numbers,
Booleans, and Agda functions over naturals and Booleans.

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

## Type of a primitive

```
typeof-base : Base → Type
typeof-base B-Nat = `ℕ
typeof-base B-Bool = `𝔹

typeof : Prim → Type
typeof (base b) = typeof-base b 
typeof (b ⇒ p) = typeof-base b ⇒ typeof p
```

## Inversion of Subtyping

Because we use algorithmic subtyping rules, the traditional inversion
lemmas for subtyping become trivial and therefore not necessary. One
can instead simply pattern match on the subtyping derivation. However,
the following inversion lemma is still useful because it hides the two
cases on the base `b`.

```
inversion-<:-base : ∀ {b A}
  → A <: typeof-base b
  → A ≡ typeof-base b
inversion-<:-base {B-Nat} <:-nat = refl
inversion-<:-base {B-Bool} <:-bool = refl
```

## Terms

We use the
[abstract-binding-trees](https://github.com/jsiek/abstract-binding-trees)
library to represent terms.

A record term is usually written

    { l₁ = M₁, ..., lᵤ = Mᵤ }

We represent a record term as follows, with the list of labels as part
of the operator.

   (op-rcd u (l₁, ..., lᵤ)) ⦅ cons (ast M₁) ... (cons (ast Mᵤ) nil) ⦆

Field access is usually written

   M.f

We instead use the notation

  M # f

because the period is a reserved symbol in Agda.

```
Var = ℕ

data Term : Set where
  `_ : Var → Term
  λ:_⇒_ : Type → Term → Term
  _·_ : Term → Term → Term
  μ_ : Term → Term
  $ : (p : Prim) → rep p → Term
  rcd : (n : ℕ) → Vec Id n → Vec Term n → Term
  _#_ : Term → Id → Term
```

## Renamings

```
Rename : Set
Rename = Var → Var

infixr 6 _•ʳ_
_•ʳ_ : Var → Rename → Rename
(y •ʳ ρ) 0 = y
(y •ʳ ρ) (suc x) = ρ x

⇑ʳ : Rename → Rename
⇑ʳ ρ x = suc (ρ x)

ext : Rename → Rename
ext ρ = 0 •ʳ ⇑ʳ ρ

idʳ : Rename
idʳ x = x

Z-shiftʳ : (0 •ʳ ⇑ʳ idʳ) ≡ idʳ
Z-shiftʳ = extensionality G
  where G : ∀ x → (0 •ʳ ⇑ʳ idʳ) x ≡ idʳ x
        G 0 = refl
        G (suc x) = refl

rename-vec : Rename → ∀{n} → Vec Term n → Vec Term n

rename : Rename → Term → Term
rename ρ (` x)          =  ` (ρ x)
rename ρ (λ: A ⇒ N)     =  λ: A ⇒ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (μ N)          = μ (rename (ext ρ) N)
rename ρ ($ p k)        = $ p k
rename ρ (rcd n fs Ms)  = rcd n fs (rename-vec ρ Ms)
rename ρ (M # f)        = (rename ρ M) # f

rename-vec ρ {zero} [] = []
rename-vec ρ {suc n} (M ∷ Ms) = rename ρ M ∷ rename-vec ρ Ms
```

## Substitution

```
Subst : Set
Subst = Var → Term

infixr 6 _•_
_•_ : Term → Subst → Subst
(M • σ) 0 = M
(M • σ) (suc x) = σ x

id : Subst
id x = ` x

↑ : Subst
↑ x = ` (suc x)

⇑ : Subst → Subst
⇑ σ x = rename suc (σ x)

exts : Subst → Subst
exts σ = (` 0) • ⇑ σ

subst-vec : Subst → ∀{n} → Vec Term n → Vec Term n

subst : (σ : Subst) → Term → Term
subst σ (` k)          =  σ k
subst σ (λ: A ⇒ N)     =  λ: A ⇒ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (μ N)          = μ (subst (exts σ) N)
subst σ ($ p k)        = $ p k
subst σ (rcd n fs Ms)  = rcd n fs (subst-vec σ Ms)
subst σ (M # f)        = (subst σ M) # f

subst-vec σ {zero} [] = []
subst-vec σ {suc n} (M ∷ Ms) = subst σ M ∷ subst-vec σ Ms

abstract
  infixr 5 _⨟_
  _⨟_ : Subst → Subst → Subst
  (σ₁ ⨟ σ₂) = λ x → subst σ₂ (σ₁ x)

  seqˢ-def : (σ₁ : Subst) → (σ₂ : Subst) (x : Var)
    → (σ₁ ⨟ σ₂) x ≡ subst σ₂ (σ₁ x)
  seqˢ-def σ₁ σ₂ x = refl
{-# REWRITE seqˢ-def #-}

_[_] : Term → Term → Term
N [ M ] =  subst (M • id) N
```

## Contexts

```
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

```
infix  4  _∋_⦂_

data _∋_⦂_ : Context → ℕ → Type → Set where

  Z : ∀ {Γ A}
      ------------------
    → Γ , A ∋ 0 ⦂ A

  S : ∀ {Γ x A B}
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , B ∋ (suc x) ⦂ A
```

## Typing judgement

The typing rules for records closely follow the rules (T-Rcd and
T-Proj) in Chapter 11 of TAPL.

```
data _⊢*_⦂_ : Context → ∀ {n} → Vec Term n → Vec Type n → Set 

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom 
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I 
  ⊢λ : ∀ {Γ N A B}
    → Γ , A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ λ: A ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  ⊢· : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  ⊢μ : ∀ {Γ M A}
    → Γ , A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ M ⦂ A

  ⊢$ : ∀{Γ p k A}
     → A ≡ typeof p
       -------------
     → Γ ⊢ $ p k ⦂ A

  ⊢rcd : ∀{Γ n}{Ms : Vec Term n}{As : Vec Type n}{fs : Vec Id n}
    → Γ ⊢* Ms ⦂ As
    → (d : distinct fs)
    →  Γ ⊢ (rcd n fs Ms) ⦂ Record n fs As {d}

  ⊢# : ∀{Γ A M n fs As d i f}
    → Γ ⊢ M ⦂ Record n fs As {d}
    → fs ❲ i ❳ ≡ f
    → As ❲ i ❳ ≡ A
      -------------
    → Γ ⊢ M # f ⦂ A

  ⊢<: : ∀{Γ M A B}
    → Γ ⊢ M ⦂ A   → A <: B
      --------------------
    → Γ ⊢ M ⦂ B

data _⊢*_⦂_ where
  ⊢*nil : ∀{Γ} → Γ ⊢* [] ⦂ []

  ⊢*cons : ∀ {n}{Γ M}{Ms : Vec Term n}{A}{As : Vec Type n}
         → Γ ⊢ M ⦂ A
         → Γ ⊢* Ms ⦂ As
         → Γ ⊢* (M ∷ Ms) ⦂ (A ∷ As)
```

## Values

```
data Value : Term → Set where

  V-λ : ∀ {A} {N : Term}
      ---------------------------
    → Value (λ: A ⇒ N)

  V-const : ∀ {p k}
      -----------------
    → Value ($ p k)

  V-rcd : ∀{n}{fs}{Ms}
    → Value (rcd n fs Ms)
```

## Frames and plug

```
data Frame : Set where
  □·_ : Term → Frame
  _·□ : (M : Term) → (v : Value M) → Frame
  rcd□ : ∀ {n : ℕ} (i : Fin n) → Vec Id n → Vec Term n → Frame
  □#_ : Id → Frame
```

The `insert` function, used in the `plug` function defined next,
replaces the ith argument in a sequence of arguments.

```
insert : ∀{n} → Term → (i : Fin n) → Vec Term n → Vec Term n
insert {suc n} M zero (M' ∷ Ms) = M ∷ Ms
insert {suc n} M (suc i) (M' ∷ Ms) = M' ∷ (insert {n} M i Ms)
```

The `plug` function fills a frame's hole with a term.

```
plug : Term → Frame → Term
plug L (□· M)             = L · M
plug M ((L ·□) v)         = L · M
plug M (rcd□ {n} i fs Ms) = (rcd n fs (insert {n} M i Ms))
plug M (□# f)          = M # f
```

## Reduction

In the following, just the β-# rule is new. It corresponds to the
following reduction rule from Chapter 11 of TAPL.

    { lᵢ = vᵢ | i ∈ 1..n }.lⱼ  —→  vⱼ

```
data _—→_ : Term → Term → Set where

  ξ : ∀ {M M′}
    → (F : Frame)
    → M —→ M′
      ---------------------
    → plug M F —→ plug M′ F

  β-λ : ∀ {A N V}
    → Value V
      -------------------------
    → (λ: A ⇒ N) · V —→ N [ V ]

  β-μ : ∀ {M}
      ----------------
    → μ M —→ M [ μ M ]

  δ : ∀ {b p f k}
      ---------------------------------------------
    → ($ (b ⇒ p) f) · ($ (base b) k) —→ ($ p (f k))

  β-# : ∀ {n}{ls : Vec Id n}{vs : Vec Term n} {lⱼ}{j : Fin n}
    → ls ❲ j ❳ ≡ lⱼ
      -----------------------------------------
    → (rcd n ls vs) # lⱼ —→  vs ❲ j ❳
```

## Canonical Forms

```
data Function : Term → Type → Set where
  Fun-λ : ∀ {A B C D}{N}
    → ∅ , A ⊢ N ⦂ B
    → A ⇒ B <: C ⇒ D
    → Function (λ: A ⇒ N) (C ⇒ D)
  Fun-prim : ∀{b p k A B}
    → typeof (b ⇒ p) <: A ⇒ B
    → Function ($ (b ⇒ p) k) (A ⇒ B)

canonical-fun : ∀{V A B}
  → ∅ ⊢ V ⦂ A ⇒ B
  → Value V
    ------------------
  → Function V (A ⇒ B)
canonical-fun (⊢λ ⊢V) vV = Fun-λ ⊢V <:-refl
canonical-fun (⊢$ {p = base B-Nat} ()) vV
canonical-fun (⊢$ {p = base B-Bool} ()) vV
canonical-fun (⊢$ {p = b ⇒ p} refl) vV = Fun-prim <:-refl
canonical-fun (⊢<: ⊢V (<:-fun {C}{D}{A}{B} A<:C D<:B)) vV
    with canonical-fun ⊢V vV
... | Fun-λ ⊢N lt = Fun-λ ⊢N (<:-trans lt (<:-fun A<:C D<:B))
... | Fun-prim lt = Fun-prim (<:-trans lt (<:-fun A<:C D<:B))
```

```
data Constant : Base → Term → Set where
  base-const : ∀{b k} → Constant b ($ (base b) k)

canonical-base : ∀{b V}
  → ∅ ⊢ V ⦂ typeof-base b
  → Value V
    ------------
  → Constant b V
canonical-base {B-Nat} (⊢$ {.∅} {base B-Nat} x) vV = base-const
canonical-base {B-Nat} (⊢<: ⊢V <:-nat) vV = canonical-base ⊢V vV
canonical-base {B-Bool} (⊢$ {.∅} {base B-Bool} x) vV = base-const
canonical-base {B-Bool} (⊢<: ⊢V <:-bool) vV = canonical-base ⊢V vV
```

```
data Rcd : Term → Type → Set where
  rcd : ∀{n}{fs : Vec Id n}{Ms : Vec Term n}{As : Vec Type n}{d : distinct fs}
         {k}{ks : Vec Id k}{Bs : Vec Type k}{d' : distinct ks}
      → ∅ ⊢* Ms ⦂ As
      → Record n fs As {d} <: Record k ks Bs {d'}
      → Rcd (rcd n fs Ms) (Record k ks Bs {d'})
```

```
canonical-rcd : ∀{V n fs As d}
   → ∅ ⊢ V ⦂ Record n fs As {d}
   → Value V
   → Rcd V (Record n fs As {d})
canonical-rcd (⊢$ {p = base B-Nat} ()) vV
canonical-rcd (⊢$ {p = base B-Bool} ()) vV
canonical-rcd (⊢rcd ⊢Ms d) vV = rcd {d = d} {d' = d} ⊢Ms <:-refl
canonical-rcd {V} {n} {fs} {As} {d} (⊢<: ⊢V (<:-rcd {d1 = d1} fs⊆fs' lt)) vV
    with canonical-rcd {d = distinct-rel d1} ⊢V vV
... | rcd {fs = fs''}{d = d''} ⊢Ms lt' = 
      rcd {d = d''}{d' = d} ⊢Ms (<:-trans lt' (<:-rcd fs⊆fs' lt))
```

## Progress

```
data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
```

```
progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢$ _)                           = done V-const
progress (⊢λ ⊢N)                          = done V-λ
progress (⊢· {L = L}{M}{A}{B} ⊢L ⊢M)
    with progress ⊢L
... | step L—→L′                          = step (ξ (□· M) L—→L′)
... | done VL
        with progress ⊢M
...     | step M—→M′                      = step (ξ ((L ·□) VL) M—→M′)
...     | done VM 
        with canonical-fun ⊢L VL 
...     | Fun-λ ⊢N lt                     = step (β-λ VM)
...     | Fun-prim {b}{p}{k} (<:-fun A<:p b<:B)
        rewrite inversion-<:-base A<:p
        with canonical-base ⊢M VM 
...     | base-const                      = step δ
progress (⊢μ ⊢M)                          = step β-μ
progress (⊢# {n = n}{fs}{As}{d}{i}{f} ⊢R lif liA)
    with progress ⊢R
... | step R—→R′                          = step (ξ (□# f) R—→R′)
... | done VR
    with canonical-rcd {d = d} ⊢R VR
... | rcd {n'}{fs'}{Ms} ⊢MS (<:-rcd fs⊆fs' lt)
    with lookup-⊆ {i = i} fs⊆fs'
... | ⟨ k , eq ⟩ rewrite eq = step (β-# {j = k} lif)
progress (⊢rcd x d)                       = done V-rcd
progress (⊢<: {A = A}{B} ⊢M A<:B)         = progress ⊢M
```

## Renaming and substitution

```
WTRename : Context → Rename → Context → Set
WTRename Γ ρ Δ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ ρ x ⦂ A
```

```
ext-pres : ∀ {Γ Δ ρ B}
  → WTRename Γ ρ Δ
    --------------------------------
  → WTRename (Γ , B) (ext ρ) (Δ , B)
ext-pres {ρ = ρ } ⊢ρ Z = Z
ext-pres {ρ = ρ } ⊢ρ (S {x = x} ∋x) =  S (⊢ρ ∋x)
```

```
rename-vec-pres : ∀ {Γ Δ ρ}{n}{Ms : Vec Term n}{As : Vec Type n}
  → WTRename Γ ρ Δ
  → Γ ⊢* Ms ⦂ As
    ---------------------
  → Δ ⊢* rename-vec ρ Ms ⦂ As
```

```
rename-pres : ∀ {Γ Δ ρ M A}
  → WTRename Γ ρ Δ
  → Γ ⊢ M ⦂ A
    ------------------
  → Δ ⊢ rename ρ M ⦂ A
rename-pres ⊢ρ (⊢` ∋w)           =  ⊢` (⊢ρ ∋w)
rename-pres {ρ = ρ} ⊢ρ (⊢λ ⊢N)   =  ⊢λ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ⊢ρ) ⊢N)
rename-pres {ρ = ρ} ⊢ρ (⊢· ⊢L ⊢M)        =  ⊢· (rename-pres {ρ = ρ} ⊢ρ ⊢L) (rename-pres {ρ = ρ} ⊢ρ ⊢M)
rename-pres {ρ = ρ} ⊢ρ (⊢μ ⊢M)   =  ⊢μ (rename-pres {ρ = ext ρ} (ext-pres {ρ = ρ} ⊢ρ) ⊢M)
rename-pres ⊢ρ (⊢$ eq)           = ⊢$ eq
rename-pres ⊢ρ (⊢rcd ⊢Ms dfs) = ⊢rcd (rename-vec-pres ⊢ρ ⊢Ms ) dfs
rename-pres {ρ = ρ} ⊢ρ (⊢# {d = d} ⊢R lif liA) = ⊢# {d = d}(rename-pres {ρ = ρ} ⊢ρ ⊢R) lif liA
rename-pres {ρ = ρ} ⊢ρ (⊢<: ⊢M lt) = ⊢<: (rename-pres {ρ = ρ} ⊢ρ ⊢M) lt

rename-vec-pres ⊢ρ ⊢*nil = ⊢*nil
rename-vec-pres {ρ = ρ} ⊢ρ (⊢*cons ⊢M ⊢Ms) =
  let IH = rename-vec-pres {ρ = ρ} ⊢ρ ⊢Ms in
  ⊢*cons (rename-pres {ρ = ρ} ⊢ρ ⊢M) IH
```

```
WTSubst : Context → Subst → Context → Set
WTSubst Γ σ Δ = ∀ {A x} → Γ ∋ x ⦂ A → Δ ⊢ subst σ (` x) ⦂ A
```

```
exts-pres : ∀ {Γ Δ σ B}
  → WTSubst Γ σ Δ
    --------------------------------
  → WTSubst (Γ , B) (exts σ) (Δ , B)
exts-pres {σ = σ} Γ⊢σ Z = ⊢` Z
exts-pres {σ = σ} Γ⊢σ (S {x = x} ∋x)
     = rename-pres {ρ = suc} S (Γ⊢σ ∋x)
     -- rewrite exts-suc-rename σ x
```

```
subst-vec-pres : ∀ {Γ Δ σ}{n}{Ms : Vec Term n}{A}
  → WTSubst Γ σ Δ
  → Γ ⊢* Ms ⦂ A
    -----------------------
  → Δ ⊢* subst-vec σ Ms ⦂ A

subst-pres : ∀ {Γ Δ σ N A}
  → WTSubst Γ σ Δ
  → Γ ⊢ N ⦂ A
    ---------------
  → Δ ⊢ subst σ N ⦂ A
subst-pres Γ⊢σ (⊢` eq)            = Γ⊢σ eq
subst-pres {σ = σ} Γ⊢σ (⊢λ ⊢N)    = ⊢λ (subst-pres{σ = exts σ}(exts-pres {σ = σ} Γ⊢σ) ⊢N) 
subst-pres {σ = σ} Γ⊢σ (⊢· ⊢L ⊢M) = ⊢· (subst-pres{σ = σ} Γ⊢σ ⊢L) (subst-pres{σ = σ} Γ⊢σ ⊢M) 
subst-pres {σ = σ} Γ⊢σ (⊢μ ⊢M)    = ⊢μ (subst-pres{σ = exts σ} (exts-pres{σ = σ} Γ⊢σ) ⊢M) 
subst-pres Γ⊢σ (⊢$ e)             = ⊢$ e 
subst-pres Γ⊢σ (⊢rcd ⊢Ms dfs) = ⊢rcd (subst-vec-pres Γ⊢σ ⊢Ms ) dfs
subst-pres {σ = σ} Γ⊢σ (⊢# {d = d} ⊢R lif liA) =
    ⊢# {d = d} (subst-pres {σ = σ} Γ⊢σ ⊢R) lif liA
subst-pres {σ = σ} Γ⊢σ (⊢<: ⊢N lt) = ⊢<: (subst-pres {σ = σ} Γ⊢σ ⊢N) lt

subst-vec-pres Γ⊢σ ⊢*nil = ⊢*nil
subst-vec-pres {σ = σ} Γ⊢σ (⊢*cons ⊢M ⊢Ms) =
    ⊢*cons (subst-pres {σ = σ} Γ⊢σ ⊢M) (subst-vec-pres Γ⊢σ ⊢Ms)
```

```
substitution : ∀{Γ A B M N}
   → Γ ⊢ M ⦂ A
   → (Γ , A) ⊢ N ⦂ B
     ---------------
   → Γ ⊢ N [ M ] ⦂ B
substitution {Γ}{A}{B}{M}{N} ⊢M ⊢N = subst-pres {σ = M • id} G ⊢N
    where
    G : ∀ {A₁ : Type} {x : ℕ}
      → (Γ , A) ∋ x ⦂ A₁ → Γ ⊢ subst (M • id) (` x) ⦂ A₁
    G {A₁} {zero} Z = ⊢M
    G {A₁} {suc x} (S ∋x) = ⊢` ∋x
```

## Plug Inversion

```
insert-inversion : ∀{n}{M}{i : Fin n}{Ms : Vec Term n}
     {As : Vec Type n}
   → ∅ ⊢* insert M i Ms ⦂ As
   → Σ[ B ∈ Type ] ∅ ⊢ M ⦂ B × (∀ M' → ∅ ⊢ M' ⦂ B → ∅ ⊢* insert M' i Ms ⦂ As)
insert-inversion {suc n} {M} {zero} {M' ∷ Ms} (⊢*cons {A = A} ⊢M ⊢Ms) =
  ⟨ A , ⟨ ⊢M , (λ M' z → ⊢*cons z ⊢Ms) ⟩ ⟩
insert-inversion {suc n} {M} {suc i} {M' ∷ Ms} (⊢*cons ⊢M ⊢Ms)
    with insert-inversion {n} {M} {i} {Ms} ⊢Ms
... | ⟨ B , ⟨ ⊢M' , imp ⟩ ⟩ = ⟨ B , ⟨ ⊢M' , (λ M' z → ⊢*cons ⊢M (imp M' z)) ⟩ ⟩
```

```
plug-inversion : ∀{M F A}
   → ∅ ⊢ plug M F ⦂ A
     ----------------------------------------------------------------
   → Σ[ B ∈ Type ] ∅ ⊢ M ⦂ B × (∀ M' → ∅ ⊢ M' ⦂ B → ∅ ⊢ plug M' F ⦂ A)
plug-inversion {M} {□· N} {A} (⊢· {A = A'} ⊢M ⊢N) =
    ⟨ A' ⇒ A , ⟨ ⊢M , (λ M' z → ⊢· z ⊢N) ⟩ ⟩
plug-inversion {M} {(L ·□) v} {A} (⊢· {A = A'} ⊢L ⊢M) =
    ⟨ A' , ⟨ ⊢M , (λ M' → ⊢· ⊢L) ⟩ ⟩
plug-inversion {F = rcd□ i fs Ms} (⊢rcd ⊢Ms dfs)
    with insert-inversion ⊢Ms
... | ⟨ A' , ⟨ ⊢M , imp ⟩ ⟩ =    
    ⟨ A' , ⟨ ⊢M , (λ M' ⊢M' → ⊢rcd (imp M' ⊢M') dfs) ⟩ ⟩
plug-inversion {F = □# f} (⊢# {n = n}{fs}{As}{d} ⊢M lif liA) =
    ⟨ Record n fs As , ⟨ ⊢M , (λ M' z → ⊢# {d = d} z lif liA) ⟩ ⟩
plug-inversion {L} {F} {B} (⊢<: ⊢M A<:B)
    with plug-inversion {L} {F} ⊢M
... | ⟨ A' , ⟨ ⊢M' , imp ⟩ ⟩ =
    ⟨ A' , ⟨ ⊢M' , (λ M' x → ⊢<: (imp M' x) A<:B) ⟩ ⟩
```

## Preservation

```
getfield-pres : ∀{n}{As : Vec Type n}{A}{Ms : Vec Term n}{i : Fin n}
         → ∅ ⊢* Ms ⦂ As
         → As ❲ i ❳ ≡ A
         → ∅ ⊢ Ms ❲ i ❳ ⦂ A
getfield-pres {i = zero} (⊢*cons ⊢M ⊢Ms) refl = ⊢M
getfield-pres {i = suc i} (⊢*cons ⊢M ⊢Ms) As[i]=A = getfield-pres ⊢Ms As[i]=A
```

```
preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve ⊢M (ξ {M}{M′} F M—→M′)
    with plug-inversion ⊢M
... | ⟨ B , ⟨ ⊢M' , plug-wt ⟩ ⟩ = plug-wt M′ (preserve ⊢M' M—→M′)
preserve (⊢μ ⊢M) β-μ = substitution (⊢μ ⊢M) ⊢M
preserve (⊢· ⊢L ⊢M) (β-λ vV)
    with canonical-fun ⊢L V-λ
... | Fun-λ ⊢N (<:-fun A2A1 BA) = ⊢<: (substitution (⊢<: ⊢M A2A1) ⊢N) BA
preserve (⊢· ⊢L ⊢M) δ
    with canonical-fun ⊢L V-const
... | Fun-prim (<:-fun A1b pA)
    rewrite inversion-<:-base A1b
    with canonical-base ⊢M V-const
... | base-const = ⊢<: (⊢$ refl) pA
preserve (⊢# {d = d}{i} ⊢R lif liA) (β-# {j = j} lif2)
    with canonical-rcd {d = d} ⊢R V-rcd
... | rcd {As = As'}{d = d'} ⊢Ms (<:-rcd fs⊆fs' As'<:As)
    with lookup-⊆ {i = i} fs⊆fs'
... | ⟨ k , fsi=fs'k ⟩
    with getfield-pres {i = k} ⊢Ms refl
... | ⊢Ms[k] 
    rewrite distinct-lookup-eq d' (trans lif2 (trans (sym lif) fsi=fs'k))
    with As'<:As {i}{j} (trans lif2 (sym lif)) 
... | lt rewrite liA = ⊢<: ⊢Ms[k] lt
preserve (⊢<: ⊢M A<:B) M—→N = ⊢<: (preserve ⊢M M—→N) A<:B
```

### Exercise `variants` (recommended)

Add variants to the language of this Chapter and update the proofs of
progress and preservation. The variant type is a generalization of a
sum type, similar to the way the record type is a generalization of
product. The following summarizes the treatement of variants in TAPL.
A variant type is traditionally written:

    〈l₁:A₁, ..., lᵤ:Aᵤ〉

The term for introducing a variant is

    〈l=t〉

and the term for eliminating a variant is

    case L of 〈l₁=x₁〉 ⇒ M₁ | ... | 〈lᵤ=xᵤ〉 ⇒ Mᵤ

The typing rules for these terms are

    (T-Variant)
    Γ ⊢ Mⱼ : Aⱼ
    ---------------------------------
    Γ ⊢ 〈lⱼ=Mⱼ〉 : 〈l₁=A₁, ... , lᵤ=Aᵤ〉


    (T-Case)
    Γ ⊢ L : 〈l₁=A₁, ... , lᵤ=Aᵤ〉
    ∀ i ∈ 1..u,   Γ,xᵢ:Aᵢ ⊢ Mᵢ : B
    ---------------------------------------------------
    Γ ⊢ case L of 〈l₁=x₁〉 ⇒ M₁ | ... | 〈lᵤ=xᵤ〉 ⇒ Mᵤ  : B

The non-algorithmic subtyping rules for variants are

    (S-VariantWidth)
    ------------------------------------------------------------
    〈l₁=A₁, ..., lᵤ=Aᵤ〉   <:   〈l₁=A₁, ..., lᵤ=Aᵤ, ..., lᵤ₊ₓ=Aᵤ₊ₓ〉

    (S-VariantDepth)
    ∀ i ∈ 1..u,    Aᵢ <: Bᵢ
    ---------------------------------------------
    〈l₁=A₁, ..., lᵤ=Aᵤ〉   <:   〈l₁=B₁, ..., lᵤ=Bᵤ〉

    (S-VariantPerm)
    ∀i∈1..u, ∃j∈1..u, kⱼ = lᵢ and Aⱼ = Bᵢ
    ----------------------------------------------
    〈k₁=A₁, ..., kᵤ=Aᵤ〉   <:   〈l₁=B₁, ..., lᵤ=Bᵤ〉
    
Come up with an algorithmic subtyping rule for variant types.


### Exercise `<:-alternative` (stretch)

Revise this formalization of records with subtyping (including proofs
of progress and preservation) to use the non-algorithmic subtyping
rules for Chapter 15 of TAPL, which we list here:

    (S-RcdWidth)
    --------------------------------------------------------------
    { l₁:A₁, ..., lᵤ:Aᵤ, ..., lᵤ₊ₓ:Aᵤ₊ₓ } <: { l₁:A₁, ..., lᵤ:Aᵤ }

    (S-RcdDepth)
        ∀i∈1..u, Aᵢ <: Bᵢ
    ----------------------------------------------
    { l₁:A₁, ..., lᵤ:Aᵤ } <: { l₁:B₁, ..., lᵤ:Bᵤ }

    (S-RcdPerm)
    ∀i∈1..u, ∃j∈1..u, kⱼ = lᵢ and Aⱼ = Bᵢ
    ----------------------------------------------
    { k₁:A₁, ..., kᵤ:Aᵤ } <: { l₁:B₁, ..., lᵤ:Bᵤ }

You will most likely need to prove inversion lemmas for the subtype relation
of the form:

    If S <: T₁ ⇒ T₂, then S ≡ S₁ ⇒ S₂, T₁ <: S₁, and S₂ <: T₂, for some S₁, S₂.

    If S <: { lᵢ : Tᵢ | i ∈ 1..n }, then S ≡ { kⱼ : Sⱼ | j ∈ 1..m }
    and { lᵢ | i ∈ 1..n } ⊆ { kⱼ | j ∈ 1..m }
    and Sⱼ <: Tᵢ for every i and j such that lᵢ = kⱼ. 

