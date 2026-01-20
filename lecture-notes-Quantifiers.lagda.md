```
module lecture-notes-Quantifiers where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
```

# Quantifiers

As we have seen, universal quantification (for all) is represented
using dependent function types.

You use (eliminate) a dependent function simply by applying it to an
argument.

```
postulate Human : Set
postulate Mortal : Human → Set
postulate Socrates : Human
postulate all-Humans-mortal : (p : Human) → Mortal p
postulate all-Humans-mortal' : ∀ p → Mortal p               -- equivalent
postulate all-Humans-mortal'' : ∀ (p : Human) → Mortal p    -- equivalent

_ : Mortal Socrates
_ = all-Humans-mortal Socrates
```

You prove a universally quantifies formula by writing a function of
the appropriate type.

```
*-0ʳ : ∀ n → n * 0 ≡ 0
*-0ʳ n rewrite *-comm n 0 = refl
```

The following shows how universals can distribute with disjunction.

```
∀-dist-⊎ : ∀ {P : Set} {Q R : P → Set}
    → (∀ (x : P) → Q x) ⊎ (∀ (x : P) → R x)
    → (∀ (x : P) → Q x ⊎ R x)
∀-dist-⊎ (inj₁ ∀x:P→Qx) x = inj₁ (∀x:P→Qx x)
∀-dist-⊎ (inj₂ ∀x:P→Rx) x = inj₂ (∀x:P→Rx x)
```

Existential quantification is represented using dependent product types.
Recall that in a dependent product type, the type of the second part
can refer to the first part.

Normal product type:

   A × B

Dependent product type:

  Σ[ x ∈ A ] B x

The values of dependent product types are good old pairs: `⟨ v₁ , v₂ ⟩`,
where `v₁ : A` and `v₂ : B v₁`.

∃ x. P x

Σ[ x ∈ ℕ ] P x

To express "there exists", the witness of the existential is the first
part of the pair. The type of the second part of the pair is some
formula involving the first part, and the value in the second part of
the pair is a proof of that formula.

```
open import Data.Product using (Σ-syntax; ∃-syntax)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
```

The following example implements a disjoint union type `A or B` using
a dependent pair.  The first part is a tag, false or true, that says
whether the payload (the second part) has type `A` or type `B`,
respectively.

```
open import Data.Bool using (Bool; true; false)

select : (A : Set) → (B : Set) → Bool → Set
select A B false = A
select A B true = B

_or_ : Set → Set → Set
A or B = Σ[ flag ∈ Bool ] select A B flag

forty-two : ℕ or (ℕ → ℕ)
forty-two = ⟨ false , 42 ⟩

inc : ℕ or (ℕ → ℕ)
inc = ⟨ true , suc ⟩

inject₁ : ∀{A B : Set} → A → A or B
inject₁ a = ⟨ false , a ⟩

inject₂ : ∀{A B : Set} → B → A or B
inject₂ b = ⟨ true , b ⟩

case : ∀{A B C : Set} → A or B → (A → C) → (B → C) → C
case ⟨ false , a ⟩ ac bc = ac a
case ⟨ true , b ⟩ ac bc = bc b
```

```
_ : 42 ≡ case forty-two (λ n → n) (λ f → f 0)
_ = refl

_ : 1 ≡ case inc (λ n → n) (λ f → f 0)
_ = refl
```

Example proofs about existentials and universals:

```
∀∃-currying1 : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ (x : A) → B x → C)
  → (Σ[ x ∈ A ] B x) → C
∀∃-currying1 f ⟨ x , y ⟩ = f x y

∀∃-currying2 : ∀ {A : Set} {B : A → Set} {C : Set}
  → ((Σ[ x ∈ A ] B x) → C)
  → (∀ (x : A) → B x → C)
∀∃-currying2 g x y = g ⟨ x , y ⟩
``` 

Example use of existentials for even numbers:

An alternative way to state that a number evenly divides another
number is using multiplication instead of repeated addition.  We shall
prove that if `m div n`, then there exists some number `k` such that
`k * m ≡ n`.  To express "there exists some number `k` such that `k *
m ≡ n`", we use the dependent produce type

    Σ[ k ∈ ℕ ] k * m ≡ n

where `k` is a name for the first part of the pair,
`ℕ` is it's type, and `k * m ≡ n` is the type
for the second part of the pair.
For example, the following proves that there exists
some number `k` such that `k * m ≡ 0`, for any `m`.

```
_ : (m : ℕ) → Σ[ k ∈ ℕ ] k * m ≡ 0
_ = λ m → ⟨ 0 , refl ⟩
```

Getting back to the alternative way to state the divides relation, the
following proof by induction shows that `m div n` implies
that there exists some `k` such that `k * m ≡ n`.

```
open import lecture-notes-Relations using (_div_; div-refl; div-step)

mdivn→k*m≡n : (m n : ℕ) → m div n → ∃[ k ] k * m ≡ n
mdivn→k*m≡n m .m (div-refl .m x) = ⟨ 1 , +-identityʳ m ⟩
mdivn→k*m≡n m .(m + n) (div-step n .m mn)
    with mdivn→k*m≡n m n mn
... | ⟨ q , q*m≡n ⟩
    rewrite sym q*m≡n =
      ⟨ (suc q) , refl ⟩
```

* For the case `div-refl`, we need to show that `k * m ≡ m`
  for some `k`. That's easy, choose `k ≡ 1`. So we
  form a dependent pair with `1` as the first part
  and a proof of `1 * m ≡ m` as the second part.

* For the case `div-step`, we need to show that `k * m ≡ m + n` for some `k`.
  The induction hypothesis tells us that `q * m ≡ n` for some `q`.
  We can get our hands on this `q` by pattern matching on the
  dependent pair returned by `mdivn→k*m≡n`, using the `with` construct.
  If we replace the `n` in the goal with `q * m`, the goal becomes
  `k * m ≡ m + q * m` which is equivalent to
  `k * m ≡ suc q * m`. We can accomplish this replacement by
  using `rewrite` with the symmetric version of the equation `q * m ≡ n`.
  Finally, we conclude the proof by choosing `suc q` as the witness
  for `k`, and `refl` for the proof that `suc q * m ≡ suc q * m`.

Going in the other direction, if we know that `n ≡ k * m`, then `m div n`
(provided `k` and `m` are not zero).

```
m-div-k*m : (k m : ℕ) → m ≢ 0 → k ≢ 0 → m div (k * m)
m-div-k*m zero m m≢0 k≢0 = ⊥-elim (k≢0 refl)
m-div-k*m (suc zero) m m≢0 _
    rewrite +-identityʳ m = div-refl m m≢0
m-div-k*m (suc (suc k)) m m≢0 _ =
    let IH = m-div-k*m (suc k) m m≢0 λ () in
    div-step (m + k * m) m IH

open import Relation.Nullary.Negation using (contradiction)

_div′_ : ℕ → ℕ → Set
m div′ n = m ≢ 0 × ∃[ k ] (k ≢ 0 × k * m ≡ n)

pattern ⟨_,_,_,_⟩ x y z w = ⟨ x , ⟨ y , ⟨ z , w ⟩ ⟩ ⟩

div′→div : ∀ (m n : ℕ) → m div′ n → m div n
div′→div m n ⟨ m≠0 , 0 , k≠0 , refl ⟩ = contradiction refl k≠0
div′→div m n ⟨ m≠0 , suc k , _ , k*m=n ⟩ rewrite sym k*m=n =
   m-div-k*m (1 + k) m m≠0 λ ()

div→div′ : ∀ (m n : ℕ) → m div n → m div′ n
div→div′ m n (div-refl .m m≠0) = ⟨ m≠0 , 1 , (λ ()) , +-identityʳ m ⟩
div→div′ m m+n (div-step n .m mdivn)
  with div→div′ m n mdivn
... | ⟨ m≠0 , k , k≠0 , km=n ⟩ =
  ⟨ m≠0 , 1 + k , (λ ()) , cong (m +_) km=n ⟩

infix 0 _⇔_

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

div⇔div′ : ∀ {m n} → m div n ⇔ m div′ n
div⇔div′ {m} {n} = record {
    to = div→div′ m n ;
    from = div′→div m n
  }
```


# Decidable

An alternative way to represent a relation is Agda is with the
relation's characteristic function. That is, a function that takes the
two elements and returns true or false, depending on whether the
elements are in the relation.

```
less-eq : ℕ → ℕ → Bool
less-eq zero n = true
less-eq (suc m) zero = false
less-eq (suc m) (suc n) = less-eq m n
```

In some sense, such a function is better than going with a data type
because it also serves as a decision procedure. However, for some
relations it is difficult or even impossible to come up with such a
function.

Sometimes its nice to link your decision procedure to the relation
defined by a data type, building the correctness of your decision
procedure into its type. The `Dec` type let's you do this by including
both the true/false regarding whether the relation holds for the input
but also the proof that it holds or that its negation holds.

```
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (_≤_)

less-eq? : (m n : ℕ) → Dec (m ≤ n)
less-eq? zero n = yes z≤n
less-eq? (suc m) zero = no (λ ())
less-eq? (suc m) (suc n)
    with less-eq? m n
... | yes m≤n = yes (s≤s m≤n)
... | no m≰n = no λ { (s≤s m≤n) →  m≰n m≤n }
```
