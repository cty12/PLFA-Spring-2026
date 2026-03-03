module Scratch2 where

open import Data.Nat
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.List using (List; []; _∷_; map; unzip; reverse; splitAt; _++_)

-- Characteristic Functions, Bool, and Decidable
open import Data.Bool using (Bool; true; false)

less-eq : ℕ → ℕ → Bool
less-eq zero n = true
less-eq (suc m) zero = false
less-eq (suc m) (suc n) = less-eq m n

open import Data.Unit using (tt)
open import Data.Bool using (T)

less-eq-refl : ∀ x → T (less-eq x x)
less-eq-refl zero = tt
less-eq-refl (suc x) = less-eq-refl x

open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (_≤_)

less-eq? : (m n : ℕ) → Dec (m ≤ n)
less-eq? zero n = yes z≤n
less-eq? (suc m) zero = no λ {()}
less-eq? (suc m) (suc n)
    with less-eq? m n
... | yes m≤n = yes (s≤s m≤n)
... | no ¬m≤n = no λ { (s≤s m≤n) → ¬m≤n m≤n}

open import Data.List using (List; []; _∷_; map; unzip)

_ : List ℕ
_ = 1 ∷ 2 ∷ []

open import Data.List using (reverse; splitAt; _++_)

rotate : ∀ {A : Set} → List A → ℕ → List A
rotate xs k
    with splitAt k xs
... | ⟨ ls , rs ⟩ = reverse (reverse ls ++ reverse rs)

open import Data.List.Properties using (reverse-++; reverse-involutive)

rotate-correct : ∀ {A : Set} (xs : List A) (k : ℕ)
   → rotate xs k ≡ (proj₂ (splitAt k xs)) ++ (proj₁ (splitAt k xs))
rotate-correct {A} xs k
    with splitAt k xs
... | ⟨ ls , rs ⟩ =
    begin
       reverse (reverse ls ++ reverse rs) ≡⟨ cong reverse (sym (reverse-++ rs ls)) ⟩
       reverse (reverse (rs ++ ls))       ≡⟨ reverse-involutive (rs ++ ls) ⟩
       rs ++ ls
    ∎
  
-- Richard Bird, Jeremy Siek

_▵_ : ∀{A B C : Set} → (A → B) → (A → C) → A → B × C
(f ▵ g) a = ⟨ (f a) , (g a) ⟩

_⊗_ : ∀{A B C D : Set} → (A → B) → (C → D) → A × C → B × D
(f ⊗ g) ⟨ a , c ⟩ = ⟨ f a , g c ⟩

-- unzip (slow)
▵-map : {A B : Set} → List (A × B) → List A × List B
▵-map xs = ((map proj₁) ▵ (map proj₂)) xs

unzip-fast : {A B : Set} → List (A × B) → List A × List B
unzip-fast [] = ⟨ [] , [] ⟩
unzip-fast (⟨ a , b ⟩ ∷ xs) =
  let ⟨ as , bs ⟩ = unzip-fast xs in
  ⟨ a ∷ as , b ∷ bs ⟩

unzip≡▵-map : ∀{A B : Set} → (xs : List (A × B))
           → unzip xs ≡ ▵-map xs
unzip≡▵-map [] = refl
unzip≡▵-map (⟨ a , b ⟩ ∷ xs) rewrite unzip≡▵-map xs = refl

open import Function using (_∘_)
open import Data.List.Properties using (map-∘)

my-map-∘ : ∀{A B C : Set}{g : B → C} {f : A → B} (xs : List A)
              → map (g ∘ f) xs ≡ map g (map f xs)
my-map-∘ [] = refl
my-map-∘{g = g}{f} (x ∷ xs) = cong (λ □ → g (f x) ∷ □) (my-map-∘ xs)

⊗-distrib-unzip : ∀{A B C D} {f : A → B} {g : C → D}
    → (xs : List (A × C))
    → (map f ⊗ map g) (unzip xs) ≡ unzip (map (f ⊗ g) xs)
⊗-distrib-unzip {f = f}{g} xs =
  begin
   (map f ⊗ map g) (unzip xs)                           ≡⟨ cong (λ □ → (map f ⊗ map g) □) (unzip≡▵-map xs) ⟩
   (map f ⊗ map g) (▵-map xs)                           ≡⟨ cong₂ ⟨_,_⟩ (sym (map-∘ xs)) ((sym (map-∘ xs))) ⟩
   ⟨ map (f ∘ proj₁) xs , map (g ∘ proj₂) xs ⟩                        ≡⟨⟩
   ⟨ map (proj₁ ∘ (f ⊗ g)) xs , map (proj₂ ∘ (f ⊗ g)) xs ⟩           ≡⟨ cong₂ ⟨_,_⟩ (map-∘ _) (map-∘ _) ⟩
   ⟨ (map proj₁) (map (f ⊗ g) xs) , (map proj₂) (map (f ⊗ g) xs) ⟩   ≡⟨⟩
   ▵-map (map (f ⊗ g) xs)                                             ≡⟨ sym (unzip≡▵-map _) ⟩ 
   unzip (map (f ⊗ g) xs)
  ∎

