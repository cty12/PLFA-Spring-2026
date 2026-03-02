module Scratch where

-- Naturals & Induction, Jan 13, 2026

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

one = suc zero
two = suc (suc zero)

add : Nat → Nat → Nat
add zero n = n
add (suc m) n = suc (add m n)

three = add two one

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

_ : add two one ≡ suc (suc (suc zero))
_ = refl

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
  using (sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning

_ : (x : ℕ) → (y : ℕ) → x + y + x ≡ 2 * x + y
_ = λ x y →
  let reason1 : x + y + x ≡ x + (y + x)
      reason1 = +-assoc x y x in
  let reason2 = cong (λ □ → (x + □)) (+-comm y x) in
  begin
    (x + y) + x
  ≡⟨ trans reason1 reason2 ⟩
    x + (x + y)
  ≡⟨ sym (+-assoc x x y)  ⟩
    (x + x) + y
  ≡⟨  cong (λ □ → (x + □) + y) ((sym (+-identityʳ x))) ⟩
    (x + (x + zero)) + y
  ≡⟨ refl ⟩
    2 * x + y
  ∎

open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

_ : (x : ℕ) → (y : ℕ) → x + y + x ≡ 2 * x + y
_ = solve 2 (λ x y → x :+ y :+ x := con 2 :* x :+ y) refl

dub : ℕ → ℕ
dub 0 = 0
dub (suc n) = suc (suc (dub n))

dub-correct : (n : ℕ) → dub n ≡ n + n
dub-correct zero = refl
dub-correct (suc n) =
  let IH : dub n ≡ n + n
      IH = dub-correct n in
  begin
    suc (suc (dub n))
  ≡⟨ cong (λ □ → suc (suc □)) IH ⟩
    suc (suc (n + n))
  ≡⟨ refl ⟩
    suc ((suc n) + n)
  ≡⟨ cong suc (+-comm (suc n) n) ⟩
    suc (n + suc n)
  ∎

gauss : ℕ → ℕ
gauss zero = 0
gauss (suc n) = suc n + gauss n

gauss-formula : (n : ℕ) → 2 * gauss n ≡ n * suc n
gauss-formula zero = refl
gauss-formula (suc n) =
  let IH : 2 * gauss n ≡ n * suc n
      IH = gauss-formula n in
  begin
    2 * gauss (suc n)
  ≡⟨ refl ⟩
    2 * (suc n + gauss n)
  ≡⟨ *-distribˡ-+ 2 (suc n) (gauss n) ⟩
    2 * (suc n) + 2 * gauss n
  ≡⟨ cong (λ □ → 2 * (suc n) + □) IH ⟩
    2 * (suc n) + n * (suc n)
  ≡⟨ EQ n ⟩
    (suc n) * suc (suc n)
  ∎
  where
  EQ = solve 1 (λ n → (con 2 :* (con 1 :+ n)) :+ (n :* (con 1 :+ n))
         := (con 1 :+ n) :* (con 1 :+ (con 1 :+ n))) refl

-- Relations, Jan. 15, 2026

data Even : ℕ → Set where
  even-0 : Even 0
  even-+2 : (n : ℕ) → Even n → Even (2 + n)

open import Data.Product
open import Data.Sum

IsEven : ℕ → Set
IsEven n = ∃[ k ] k + k + k ≡ n

_ : Even 0
_ = even-0

_ : Even 2
_ = even-+2 0 even-0

even-dub : (n : ℕ) → Even (n + n)
even-dub zero = even-0
even-dub (suc n) =
  let IH : Even (n + n)
      IH = even-dub n in
  let tmp : Even (suc (suc (n + n)))
      tmp = even-+2 (n + n) IH in
  let eq : (n + suc n) ≡ suc (n + n)
      eq = +-suc n n in
  subst (λ □ → Even (suc □)) (sym eq) tmp

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Empty using (⊥-elim)

inv-Even : (n m : ℕ) → Even m → m ≢ 0 → suc (suc n) ≡ m → Even n
inv-Even n m even-0 mnz eq = ⊥-elim (mnz refl)
  -- suc (suc n) ≡ 0
  -- 0 ≢ 0 = (0 ≡ 0 → ⊥)
inv-Even n m (even-+2 k even-m) mnz refl = even-m

data _div_ : ℕ → ℕ → Set where
  div-refl : (m : ℕ) → m ≢ 0 → m div m
  div-step : (n m : ℕ) → m div n → m div (m + n)

3-div-3 : 3 div 3
3-div-3 = div-refl 3 λ {()}

3-div-6 : 3 div 6
3-div-6 = div-step 3 3 3-div-3

div-+ : ∀ l m k → l div m → l div k → l div (m + k)
div-+ l .l k (div-refl .l l≢0) lk = div-step k l lk
div-+ l .(l + m) k (div-step m .l lm) lk
   rewrite +-assoc l m k =
   let IH = div-+ l m k lm lk in
   div-step (m + k) l IH

div-trans : ∀ l m n → l div m → m div n → l div n
div-trans l m n ldivm (div-refl .m x) = ldivm
div-trans l m n ldivm (div-step k .m mdivn) =
  let IH : l div k
      IH = div-trans l m k ldivm mdivn in
  div-+ l m k ldivm IH

  
-- Equality

-- "definitional equality"   (built in & automatic)

-- "propositional equality"

data _≡ʲ_ {A : Set} (x : A) : A → Set where
  reflʲ : x ≡ʲ x

_ : _≡ʲ_ {ℕ} 0 0
_ = reflʲ

-- x+0=x : ∀ x → x + 0 ≡ x
-- x+0=x zero = refl
-- x+0=x (suc x) =
--   let IH = x+0=x x in
--   cong (λ □ → suc □) IH

x+0=x : ∀ x → x + 0 ≡ x
x+0=x x = +-identityʳ x

-- symmetric

x=x+0 : ∀ x → x ≡ x + 0
x=x+0 x = sym (x+0=x x)

-- congruence

eg-cong : ∀ x → (0 + x) + x ≡ (x + 0) + x
eg-cong x = cong (λ □ → □ + x) (x=x+0 x)

-- transitive

_ : ∀ x → (0 + x) + x ≡ 2 * x
_ = λ x →
   let eq : (x + 0) + x ≡ x + (0 + x)
       eq = +-assoc x 0 x in
   let eq2 : x + (0 + x) ≡ x + (x + 0)
       eq2 = cong (λ □ → x + □) (x=x+0 x) in
   trans (eg-cong x) (trans (+-assoc x 0 x) (cong (λ □ → x + □) (x=x+0 x)))

_ : ∀ x → (0 + x) + x ≡ 2 * x
_ = λ x →
    begin
      (0 + x) + x    ≡⟨ cong (λ □ → □ + x) (x=x+0 x) ⟩
      (x + 0) + x    ≡⟨ +-assoc x 0 x ⟩
      x + (0 + x)    ≡⟨ cong (λ □ → x + □) (x=x+0 x) ⟩
      x + (x + 0)    ≡⟨ refl ⟩
      2 * x
    ∎

-- subst

open import Relation.Binary.PropositionalEquality using (subst)

-- rewrite

even-dub'' : (n m : ℕ) → m + m ≡ n → Even n
even-dub'' n m eq rewrite (sym eq) = even-dub m

-- Isomorphism

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

×-comm : ∀{A B : Set} → A × B ≃ B × A
×-comm = record {
  to = λ { ⟨ a , b ⟩ → ⟨ b , a ⟩ };
  from = λ { ⟨ b , a ⟩ → ⟨ a , b ⟩ };
  from∘to = λ { ⟨ a , b ⟩ → refl };
  to∘from = λ { ⟨ b , a ⟩ → refl}
  }

-- C-u C-u   (fully normalize)
-- then
-- C-c C-,   (show goal)

open import Data.Bool using (Bool; true; false)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

_ : ∀{A B : Set} → ((A → B) × (A → B) ≃ ((A × Bool) → B))
_ = record {
     to = λ { ⟨ f , g ⟩ ⟨ a , false ⟩ → g a ;
              ⟨ f , g ⟩ ⟨ a , true ⟩ → f a } ; 
     from = λ h → ⟨ (λ a → h ⟨ a , true ⟩) , (λ a → h ⟨ a , false ⟩) ⟩ ;
     from∘to = λ { ⟨ f , g ⟩ → refl }; -- C-a (auto)
     to∘from = λ h → extensionality λ { ⟨ a , false ⟩ → refl ;
                                        ⟨ a , true ⟩ → refl}
     }


--- Curry-Howard Correspondence:
--- Proposition ≈ Type
--- Proof       ≈ Program

variable P Q R S : Set

-- Connectives

-- True ≈ Unit

open import Data.Unit using (⊤; tt)

_ : ⊤
_ = tt

-- Implication ≈ Function Type

-- Introduction: λ   (how to prove an implication)
_ : P → P
_ = λ p → p

-- Elimination: application   (how to use an implication)
_ : (⊤ → P) → P
_ = λ f → (f tt)

_ : P → (⊤ → P)
_ = λ p → λ x → p

-- Logical And ≈ Pair Type (Product Type)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

-- Use an And by proj₁, proj₂ (elimination)
_ : P × Q → Q × P
_ = λ pq → let p = proj₁ pq in let q = proj₂ pq in ⟨ q , p ⟩

_ : P × Q → Q × P
_ = λ { ⟨ p , q ⟩ → ⟨ q , p ⟩}

_ : (P → Q) × (Q → R) → (P → R)
_ = λ { ⟨ p→q , q→r ⟩ p → let q = p→q p in q→r q } 

_ : ((P → Q → R) × (P → Q) × P) → R
_ = λ { ⟨ pqr , ⟨ pq , p ⟩ ⟩ → let q = pq p in pqr p q}

-- Logical Or ≈ Disjoint Union Type (Sum Type)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- use a logical or by cases
_ : P ⊎ Q → Q ⊎ P
_ = λ { (inj₁ p) → inj₂ p ;
        (inj₂ q) → inj₁ q }

_ : (P → Q) × (R → Q) → ((P ⊎ R) → Q)
_ = λ { ⟨ pq , rq ⟩ (inj₁ p) → pq p ;
        ⟨ pq , rq ⟩ (inj₂ r) → rq r }

f : (P → Q) × (R → Q) → ((P ⊎ R) → Q)
f ⟨ pq , rq ⟩ (inj₁ p) = pq p
f ⟨ pq , rq ⟩ (inj₂ r) = rq r

-- False ≈ Empty     (no inhabitants)
open import Data.Empty using (⊥)

0≡1→⊥ : 0 ≡ 1 → ⊥
0≡1→⊥ = λ { ()}  -- the absurd pattern

open import Data.Empty using (⊥-elim)

_ : 0 ≡ 1 → P
_ = λ eq → ⊥-elim (0≡1→⊥ eq) -- principle of explosion

-- Negation = Implies False
open import Relation.Nullary using (¬_)

_ : (¬ P) ≡ (P → ⊥)
_ = refl

_ : P → (¬ P) → ⊥
_ = λ p np → np p

_ : P → (¬ P) → Q
_ = λ p np → ⊥-elim (np p)

open import Relation.Nullary.Negation using (contradiction)

_ : P → (¬ P) → Q
_ = λ p ¬p → contradiction p ¬p
