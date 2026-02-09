```
module lecture-notes-Lists where
```

```
open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
```

# Lists

Agda provides Lisp-style lists, with nil and cons, spelled `[]` and `_∷_`.
For example:

```
open import Data.List using (List; []; _∷_; map; unzip)

_ : List ℕ
_ = 1 ∷ 2 ∷ []
```

Agda provides lots of standard functions on lists, such as append
(`_++_`), `map`, `foldr`, `foldl`, `zip`, `unzip`, `reverse`,
`splitAt`, and many more. The Agda standard library also provides many
theorems about these functions.  We shall study some examples that use
some of these functions and theorems.

Consider the operation that rotates the elements of a list to the left
by `k` positions, with wrap-around. For example, the following rotates
by two positions to the left.

    rotate (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) 2 ≡ (3 ∷ 4 ∷ 1 ∷ 2 ∷ [])

One clever way to rotate a list is to split it into two parts, reverse
each part, append them, and then reverse again. For example, breaking
down the above example rotation into these steps:

    splitAt 2 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ ⟨ 1 ∷ 2 ∷ [] , 3 ∷ 4 ∷ [] ⟩
    reverse (1 ∷ 2 ∷ []) ≡ (2 ∷ 1 ∷ [])
    reverse (3 ∷ 4 ∷ []) ≡ (4 ∷ 3 ∷ [])
    reverse (2 ∷ 1 ∷ 4 ∷ 3 ∷ []) ≡ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []

```
open import Data.List using (reverse; splitAt; _++_)

rotate : ∀ {A : Set} → List A → ℕ → List A
rotate xs k
    with splitAt k xs
... | ⟨ ls , rs ⟩ = reverse (reverse ls ++ reverse rs)
```

Here are a few examples of `rotate` in action.

```
_ : rotate (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) 1 ≡ (2 ∷ 3 ∷ 4 ∷ 1 ∷ [])
_ = refl

_ : rotate (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) 2 ≡ (3 ∷ 4 ∷ 1 ∷ 2 ∷ [])
_ = refl

_ : rotate (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) 3 ≡ (4 ∷ 1 ∷ 2 ∷ 3 ∷ [])
_ = refl

_ : rotate (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) 4 ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
_ = refl
```

One way to think about `rotate` is in terms of swapping the part of
the list at the front with the rest of the list at the back. In the
following, the first three elements, `a , b , c`, are moved to the
back, swapping places with the `d , e`.

    rotate ([ a , b , c ] ++ [ d , e ]) 3
          ≡ [ d , e ] ++ [ a , b , c ]

With this view in mind, we can prove that `rotate` is correct using the
following two equations from the Agda standard library about `reverse` and `append`.

    reverse-++ : ∀ xs ys → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
    reverse-involutive : ∀ xs → reverse (reverse xs) ≡ xs

```
open import Data.List.Properties using (reverse-++; reverse-involutive)

rotate-correct : ∀ {A : Set} {xs ls rs : List A} {k : ℕ}
   → rotate xs k ≡ (proj₂ (splitAt k xs)) ++ (proj₁ (splitAt k xs))
rotate-correct {A}{xs}{ls}{rs}{k}
    with splitAt k xs
... | ⟨ ls , rs ⟩ =
     begin
        reverse (reverse ls ++ reverse rs)   ≡⟨ cong reverse (sym (reverse-++ rs ls)) ⟩
        reverse (reverse (rs ++ ls))         ≡⟨ reverse-involutive _ ⟩
        rs ++ ls
     ∎
```

There are many more operations and theorems in the works of Richard
Bird concerning the interactions between lists, functions, pairs, and
sums. In the following we will introduce a couple of these operations
and prove some theorems about them.  To begin, we define the fork (`▵`)
and cross (`⊗`) functions.

```
_▵_ : ∀{A B C : Set} → (A → B) → (A → C) → A → B × C
(f ▵ g) a = ⟨ (f a) , (g a) ⟩

_⊗_ : ∀{A B C D : Set} → (A → B) → (C → D) → A × C → B × D
(f ⊗ g) ⟨ a , c ⟩ = ⟨ f a , g c ⟩
```

Recall that `unzip` converts a list of pairs `xs` into a pair of
lists.  One way to implement `unzip` is to 1) `map` the `proj₁`
function over `xs`, 2) `map` the `proj₂` over `xs` and 3) pair the two
resulting lists. This can be expressed using fork in the following
way.

```
▵-map : {A B : Set} → List (A × B) → List A × List B
▵-map xs = ((map proj₁) ▵ (map proj₂)) xs
```

This implementation of `unzip` is obviously correct but not very
efficient because it makes two passes over the list of pairs. The real
implementation is more clever and makes only a single pass over the
list of pairs, as shown below. (The `unzip` in the Agda standard
library is equivalent to the following `unzip-fast`, but it is
implemented in terms of a more general function named `unzipWith`.)

```
unzip-fast : {A B : Set} → List (A × B) → List A × List B
unzip-fast [] = ⟨ [] , [] ⟩
unzip-fast (⟨ a , b ⟩ ∷ xs) =
  let ⟨ as , bs ⟩ = unzip-fast xs in
  ⟨ a ∷ as , b ∷ bs ⟩
```

The fast and slow versions of unzip are equivalent, which is
straightforward to prove by induction on the input list `xs`.

```
unzip≡▵-map : ∀{A B : Set} → (xs : List (A × B))
           → unzip xs ≡ ▵-map xs
unzip≡▵-map [] = refl
unzip≡▵-map (⟨ a , b ⟩ ∷ xs) rewrite unzip≡▵-map xs = refl
```

Next consider a simplified version of the `map-∘ theorem from
the standard library. It says that mapping functions `f` then `g` over
a list is equivalent to mapping the composition `g ∘ f` over the list.

```
open import Function using (_∘_)
open import Data.List.Properties using (map-∘)

my-map-∘ : ∀{A B C : Set}{g : B → C} {f : A → B} (xs : List A)
              → map (g ∘ f) xs ≡ map g (map f xs)
my-map-∘ []       = refl
my-map-∘ (x ∷ xs) = cong (_ ∷_) (my-map-∘ xs)
```

The cross of `map f` and `map g` commutes with `unzip` in the
following sense, which we prove with a direct equational proof.
(No induction needed.)

```
⊗-distrib-unzip : ∀{A B C D} {f : A → B} {g : C → D}
    → (xs : List (A × C))
    → (map f ⊗ map g) (unzip xs) ≡ unzip (map (f ⊗ g) xs)
⊗-distrib-unzip {A}{B}{C}{D}{f}{g} xs =                        begin
  (map f ⊗ map g) (unzip xs)                                   ≡⟨ cong (map f ⊗ map g) (unzip≡▵-map xs) ⟩
  (map f ⊗ map g) (((map proj₁) ▵ (map proj₂)) xs)             ≡⟨⟩
  ⟨ (map f ∘ map proj₁) xs , (map g ∘ map proj₂) xs ⟩          ≡⟨ cong₂ ⟨_,_⟩ (sym (map-∘ xs)) (sym (map-∘ xs)) ⟩
  ⟨ map (f ∘ proj₁) xs , map (g ∘ proj₂) xs ⟩                  ≡⟨⟩
  ⟨ map (proj₁ ∘ (f ⊗ g)) xs , map (proj₂ ∘ (f ⊗ g)) xs ⟩      ≡⟨ cong₂ ⟨_,_⟩ (map-∘ xs) (map-∘ xs) ⟩ 
  ⟨ map proj₁ (map (f ⊗ g) xs) , map proj₂ (map (f ⊗ g) xs) ⟩  ≡⟨⟩ 
  (map proj₁ ▵ map proj₂) (map (f ⊗ g) xs)                     ≡⟨ sym (unzip≡▵-map (map (f ⊗ g) xs)) ⟩ 
  unzip (map (f ⊗ g) xs)                                       ∎
```
The above proof proceeds as follows.
1. Apply `unzip≡▵-map` to replace `unzip` with a fork and two maps.
2. To get `xs` next to the maps, we unfold the definition of fork .
3. To fuse `f` and `proj₁` on the  left and `g` and `proj₂` on the right,
   we apply `map-∘` in reverse.
4. Use the definition of cross to change `f ∘ proj₁` into
   `proj₁ ∘ (f ⊗ g)`, and similarly for `g ∘ proj₂`.
5. Apply `map-∘`, separating `proj₁` from `f ⊗ g` on the
   left and `proj₂` from `f ⊗ g` on the right.
6. Apply `unzip≡▵-map` a second time, in reverse,
   to replace the fork and two maps with `unzip`.

