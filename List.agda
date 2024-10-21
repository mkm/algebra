{-# OPTIONS --cubical --prop #-}
module List where

open import Path
open import Logic
open import Product using (_×_; _,_)
open import String
open import Show

data List (A : Type) : Type where
  [] : List A
  _∷_ : A → List A → List A

infixr 30 _∷_

map : ∀ {A B} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : {A B : Type} → B → (A → B → B) → List A → B
foldr nil cons [] = nil
foldr nil cons (x ∷ xs) = cons x (foldr nil cons xs)

_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

infixr 30 _++_

++-[]-right : ∀ {A} (xs : List A) → xs ++ [] ≡ xs
++-[]-right [] _ = []
++-[]-right (x ∷ xs) i = x ∷ ++-[]-right xs i

_∼_ : ∀ {A} → List A → List A → Type
[] ∼ [] = ♯ ⊤
[] ∼ (_ ∷ _) = ♯ ⊥
(_ ∷ _) ∼ [] = ♯ ⊥
(x ∷ xs) ∼ (y ∷ ys) = (x ≡ y) × (xs ∼ ys)

∼-id : ∀ {A} (xs : List A) → xs ∼ xs
∼-id [] = lift top
∼-id (x ∷ xs) = id , ∼-id xs

encode : ∀ {A} {xs ys : List A} → xs ≡ ys → xs ∼ ys
encode {xs = xs} p = transport (t ⊢ xs ∼ p t) (∼-id xs)

decode : ∀ {A} {xs ys : List A} → xs ∼ ys → xs ≡ ys
decode {xs = []} {ys = []} e _ = []
decode {xs = x ∷ xs} {ys = y ∷ ys} (e , es) i = e i ∷ decode es i

instance
  show-List : ∀ {A} ⦃ _ : Show A ⦄ → Show (List A)
  Show.show show-List = foldr "[]" λ x s → show x ⋯ " ∷ " ⋯ s 

  show-path-List : ∀ {A} ⦃ _ : ShowPath A ⦄ → ShowPath (List A)
  Show.show show-path-List p = "LIST"
