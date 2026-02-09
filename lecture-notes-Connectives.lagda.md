```
module lecture-notes-Connectives where
```

```
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

# Connectives

Propositions as Types:

* true is unit type,
* implication is function type.
* conjunction is product (i.e. pair),
* disjunction is sum (i.e. disjoint union),
* false is empty type,

In this setting, a proposition is true if the corresponding type is
inhabited. So we can prove that a proposition is true by constructing
an inhabitant of the corresponding type.

For purposes of discussion, we'll use the letters `P`, `Q`, `R`, and `S`
for arbitrary propositions.

```
variable P Q R S : Set
```

## True

True is the unit type, written `⊤`.

It has one constructor `tt` that has no parameters,
so it is trivial to prove `⊤`.

```
open import Data.Unit using (⊤; tt)

_ : ⊤
_ = tt
```

## Implication

Implication is the function type.

So its introduction form is lambda abstraction
and the elimination form is application.

```
_ : P → P
_ = λ p → p
```

Any proposition `P` is isomorphic to `⊤ → P`.

```
_ : (⊤ → P) → P
_ = λ f → f tt

_ : P → (⊤ → P)
_ = λ p → λ tt → p
```

## Logical And (Conjunction)

Logical "and" is the pair type, written `P × Q`.

It has one constructor `⟨_,_⟩` that takes two arguments,
one for `P` and the other for `Q`.

It has two eliminators (accessors) `proj₁` and `proj₂`,
that return the proofs of `P` and of `Q`, respectively.
Alternatively, you can use pattern matching to eliminate pairs.

```
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

_ : P × Q → Q × P
_ = λ pq → ⟨ proj₂ pq , proj₁ pq ⟩
```

Here are a few proofs involving conjunction and implication
(that is, programs involving pairs and functions).

```
_ : (P × Q → R) → (Q → P → R)
_ = λ pq→r q p → pq→r ⟨ p , q ⟩

_ : (P → Q) × (Q → R) → (P → R)
_ = λ { ⟨ p→q , q→r ⟩ p →
      let q = p→q p in
      q→r q
      }

_ : ((P → Q → R) × (P → Q) × P) → R
_ = λ { ⟨ p→q→r , ⟨ p→q , p ⟩ ⟩ →
       let q→r = p→q→r p in
       let q = p→q p in
       q→r q
       }
```


## Logical Or (Disjunction)

Logical "or" is the disjoint union type, written `P ⊎ Q` (aka. the Sum type).

It has two constructors, `inl` and `inr` that take one parameter.

Elimination is by pattern matching.

```
open import Data.Sum using (_⊎_; inj₁; inj₂)

_ : P ⊎ Q → Q ⊎ P
_ = λ { (inj₁ p) → (inj₂ p);
        (inj₂ q) → (inj₁ q)}

_ : (P → Q) × (R → Q) → ((P ⊎ R) → Q)
_ = λ pq,rq → λ{ (inj₁ p) → (proj₁ pq,rq) p ;
                 (inj₂ r) → (proj₂ pq,rq) r }
```

Alternatively, one can use top-level function definitions and pattern
matching:

```
f : (P → Q) × (R → Q) → ((P ⊎ R) → Q)
f ⟨ pq , rq ⟩ (inj₁ p) = pq p
f ⟨ pq , rq ⟩ (inj₂ r) = rq r
```

## False

False is the empty type, written `⊥`.

It has no constructors. However, it can appears as the return type of
a function whose input is absurd, as in the following example.

```
open import Data.Empty using (⊥)

0≡1→⊥ : 0 ≡ 1 → ⊥
0≡1→⊥ = λ ()
```

False has one eliminator, `⊥-elim`, which has type `∀{P} → ⊥ → P`.
So one can prove anything from false.

```
open import Data.Empty using (⊥-elim)

_ : 0 ≡ 1 → P
_ = λ 0≡1 → ⊥-elim (0≡1→⊥ 0≡1)
```

## Negation

Negation is shorthand for "implies false".
Thus, one can prove false from a contradiction.

```
open import Relation.Nullary using (¬_)

_ : (¬ P) ≡ (P → ⊥)
_ = refl

_ : P → (¬ P) → ⊥
_ = λ p ¬p → ¬p p

open import Relation.Nullary.Negation using (contradiction)

_ : P → (¬ P) → ⊥
_ = λ p ¬p → contradiction p ¬p
```


