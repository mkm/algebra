{-# OPTIONS --cubical --prop #-}
module FreeMonoid where

open import Path
open import Cubical.Foundations.Isomorphism
open import Unit
open import Product
open import Nat using (ℕ)
open import List using (List; []; _∷_; _++_)

module G where
  data Grade : Type where
    * : Grade
    ε : Grade
    _·_ : Grade → Grade → Grade
    ·-ε-left : ∀ α → ε · α ≡ α
    ·-ε-right : ∀ α → α · ε ≡ α
    ·-assoc : ∀ α β γ → (α · β) · γ ≡ α · (β · γ)
    Grade-set : is-set Grade

  Free : Type → Grade → Type
  Free A * = A
  Free A ε = Unit
  Free A (α · β) = Free A α × Free A β
  Free A (·-ε-left α i) = ×-Unit-left (Free A α) i
  Free A (·-ε-right α i) = ×-Unit-right (Free A α) i
  Free A (·-assoc α β γ i) = ×-assoc (Free A α) (Free A β) (Free A γ) i
  Free A (Grade-set x y p q i j) = {!!}

{-
  transform : Type → Grade → Type
  transform A * = Free A *
  transform A ε = Free A ε
  transform A (α · β) = Free A
  transform A (·-assoc α α₁ α₂ i) = {!!}

  lift : ∀ {A α β} → α ≡ β → Free A α ≡ Free A β
  lift p = {!!}
-}

infix 60 _·_

{-
record Free (A : Type) : Type where
  field
    grade : G.Grade
    struct : G.Free A grade

open Free

⟨_⟩ : ∀ {A} → A → Free A
grade ⟨ x ⟩ = G.*
struct ⟨ x ⟩ = x

ε : ∀ {A} → Free A
grade ε = G.ε
struct ε = unit

_·_ : ∀ {A} → Free A → Free A → Free A
grade (x · y) = grade x G.· grade y
struct (x · y) = struct x , struct y

·-assoc : ∀ {A} (x y z : Free A) → (x · y) · z ≡ x · (y · z)
grade (·-assoc x y z i) = G.·-assoc (grade x) (grade y) (grade z) i
struct (·-assoc {A} x y z i) = glue (λ { (i = i0) → elem₀ ; (i = i1) → elem₁ }) elem₁
  where
    elem₀ : (G.Free A (grade x) × G.Free A (grade y)) × G.Free A (grade z)
    elem₀ = (struct x , struct y) , struct z
    elem₁ : G.Free A (grade x) × (G.Free A (grade y) × G.Free A (grade z))
    elem₁ = struct x , (struct y , struct z)
-}

{-
data F (A : Type) : Type₁ where
  ⟨_⟩ : A → F A
  ε : F A
  _·_ : F A → F A → F A
  ·-ε-left : ∀ x → ε · x ≡ x
  ·-ε-right : ∀ x → x · ε ≡ x
  assoc : ∀ x y z → (x · y) · z ≡ x · (y · z)
  is-poly-set : (f g : {B : Type} → B → F B) (p q : f ≡ g) → p ≡ q
-}

data M (A : Type) : Type where
  ⟨_⟩ : A → M A
  ε : M A
  _·_ : M A → M A → M A
  ·-ε-left : ∀ x → ε · x ≡ x
  ·-ε-right : ∀ x → x · ε ≡ x
  ·-assoc-⟨⟩ : ∀ a x y → (⟨ a ⟩ · x) · y ≡ ⟨ a ⟩ · (x · y)

data Can₁ {A : Type} : M A → Type where
  c-⟨⟩ : ∀ {a} → Can₁ ⟨ a ⟩
  c-· : ∀ {x y} → Can₁ x → Can₁ y → Can₁ (x · y)

data Can {A : Type} : M A → Type where
  c-ε : Can ε
  c-1 : ∀ {x} → Can₁ x → Can x

·-can : ∀ {A} {x y : M A} → Can x → Can y → Can (x · y)
·-can {A} c-ε c-ε = transp (λ t → Can {A} (·-ε-left ε (~ t))) i0 c-ε
·-can {y = y} c-ε (c-1 c₂) = c-1 (transp (λ t → Can₁ (·-ε-left y (~ t))) i0 c₂) 
·-can {x = x} (c-1 c₁) c-ε = c-1 (transp (λ t → Can₁ (·-ε-right x (~ t))) i0 c₁)
·-can (c-1 c₁) (c-1 c₂) = c-1 (c-· c₁ c₂)

·-can-ε-left : ∀ {A} {x : M A} (c : Can x) → ·-can c-ε c =⟦( λ i → Can (·-ε-left x i) )⟧= c
·-can-ε-left c-ε = {!!}
·-can-ε-left (c-1 c) = {!!}

all-can : ∀ {A} (x : M A) → Can x
all-can ⟨ a ⟩ = c-1 c-⟨⟩
all-can ε = c-ε
all-can (x · y) = ·-can (all-can x) (all-can y)
all-can (·-ε-left x i) = ·-can-ε-left (all-can x) i
all-can (·-ε-right x i) = {!!}
all-can (·-assoc-⟨⟩ a x y i) = {!!}

_·′_ : ∀ {A} → M A → M A → M A
⟨ a ⟩ ·′ y = ⟨ a ⟩ · y
ε ·′ y = y
(x₁ · x₂) ·′ y = x₁ ·′ (x₂ ·′ y)
·-ε-left x _ ·′ y = x ·′ y
·-ε-right x _ ·′ y = x ·′ y
·-assoc-⟨⟩ a x₁ x₂ _ ·′ y = ⟨ a ⟩ · (x₁ ·′ (x₂ ·′ y))

infix 60 _·′_

·-path : ∀ {A} (x y : M A) → x · y ≡ x ·′ y
·-path ⟨ a ⟩ y _ = ⟨ a ⟩ · y
·-path ε y = ·-ε-left y
·-path (x₁ · x₂) y = (λ i → (·-path x₁ x₂ i) · y) ∘ {!!}
·-path (·-ε-left x i) y = {!!}
·-path (·-ε-right x i) y = {!!}
·-path (·-assoc-⟨⟩ a x₁ x₂ i) y = {!!}

·′-assoc : ∀ {A} (x y z : M A) → (x ·′ y) · z ≡ x ·′ (y · z)
·′-assoc ⟨ a ⟩ y z = {!!}
·′-assoc ε y z = {!!}
·′-assoc (x₁ · x₂) y z = {!!}
·′-assoc (·-ε-left x i) y z = {!!}
·′-assoc (·-ε-right x i) y z = {!!}
·′-assoc (·-assoc-⟨⟩ a x₁ x₂ i) y z = {!!}

·′-ε-right : ∀ {A} (x : M A) → x ·′ ε ≡ x
·′-ε-right ⟨ a ⟩ = ·-ε-right ⟨ a ⟩
·′-ε-right ε _ = ε
·′-ε-right (x · y) = {!!}
·′-ε-right (·-ε-left x i) = {!!}
·′-ε-right (·-ε-right x i) = {!!}
·′-ε-right (·-assoc-⟨⟩ a x y i) = {!!}

·-assoc : ∀ {A} (x y z : M A) → (x · y) · z ≡ x · (y · z)
·-assoc ⟨ a ⟩ y z = ·-assoc-⟨⟩ a y z
·-assoc ε y z = (λ i → ·-ε-left y i · z) ∘ (λ i → ·-ε-left (y · z) (~ i))
·-assoc (x₁ · x₂) y z =
  ((λ i → ·-assoc x₁ x₂ y i · z) ∘ (λ i → ·-assoc x₁ (x₂ · y) z i)) ∘₃
  (λ i → x₁ · ·-assoc x₂ y z i) ∘₃
  (λ i → ·-assoc x₁ x₂ (y · z) (~ i))
·-assoc (·-ε-left x i) y z = {!·-assoc (·-ε-left x i0) y z!}
-- (j = 0) → (·-ε-left x i · y) · z
-- (j = 1) → ·-ε-left x i · (y · z)
-- (i = 0) → ·-assoc (ε · x) y z j
-- (i = 1) → ·-assoc x y z j
-- (i = 0) (j = 0) → ((ε · x) · y) · z
-- (i = 0) (j = 1) → (ε · x) · (y · z)
-- (i = 1) (j = 0) → (x · y) · z
-- (i = 1) (j = 1) → x · (y · z)
·-assoc (·-ε-right x i) y z = {!!}
·-assoc (·-assoc-⟨⟩ a x₁ x₂ i) y z = {!·-assoc (·-assoc-⟨⟩ a x₁ x₂ i0) y z!}

from-list : ∀ {A} → List A → M A
from-list [] = ε
from-list (x ∷ xs) = ⟨ x ⟩ · from-list xs

prepend : ∀ {A} → M A → List A → List A
prepend ⟨ a ⟩ ys = a ∷ ys
prepend ε ys = ys
prepend (x · y) ys = prepend x (prepend y ys)
prepend (·-ε-left x _) ys = prepend x ys
prepend (·-ε-right x i) ys = prepend x ys
prepend (·-assoc-⟨⟩ a x y i) ys = a ∷ prepend x (prepend y ys)

to-list : ∀ {A} → M A → List A
to-list x = prepend x []

from-prepend′ : ∀ {A} (x : M A) (ys : List A) → from-list (prepend x ys) ≡ x ·′ from-list ys
from-prepend′ ⟨ a ⟩ ys _ = ⟨ a ⟩ · from-list ys
from-prepend′ ε ys _ = from-list ys
from-prepend′ (x · y) ys =
  from-prepend′ x (prepend y ys) ∘
  (λ i → x ·′ from-prepend′ y ys i)
from-prepend′ (·-ε-left x i) ys = {!!}
from-prepend′ (·-ε-right x i) ys = {!!}
from-prepend′ (·-assoc-⟨⟩ a x y i) ys = {!!}

from-prepend : ∀ {A} (x : M A) (ys : List A) → from-list (prepend x ys) ≡ x · from-list ys
from-prepend ⟨ a ⟩ ys _ = ⟨ a ⟩ · from-list ys
from-prepend ε ys i = ·-ε-left (from-list ys) (~ i)
from-prepend (x · y) ys =
  from-prepend x (prepend y ys) ∘₃
  (λ i → x · from-prepend y ys i) ∘₃
  (λ i → ·-assoc x y (from-list ys) (~ i))
from-prepend (·-ε-left x i) ys = {!from-prepend (·-ε-left x i0) ys!}
from-prepend (·-ε-right x i) ys = {!!}
from-prepend (·-assoc-⟨⟩ a x y i) ys = {!!}

from-to-list : ∀ {A} (x : M A) → from-list (to-list x) ≡ x
from-to-list x = from-prepend x [] ∘ ·-ε-right x

prepend-from-list : ∀ {A} (xs ys : List A) → prepend (from-list xs) ys ≡ xs ++ ys
prepend-from-list [] ys _ = ys
prepend-from-list (x ∷ xs) ys i = x ∷ prepend-from-list xs ys i

to-from-list : ∀ {A} (xs : List A) → to-list (from-list xs) ≡ xs
to-from-list xs = prepend-from-list xs [] ∘ List.++-[]-right xs

list-equiv : ∀ A → M A ≃ List A
list-equiv A = isoToEquiv φ
  where
    φ : Iso (M A) (List A)
    Iso.fun φ = to-list
    Iso.inv φ = from-list
    Iso.rightInv φ = to-from-list
    Iso.leftInv φ = from-to-list

list-path : M ≡ List
list-path i A = univ (list-equiv A) i
