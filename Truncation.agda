{-# OPTIONS --cubical --prop #-}
module Truncation where

open import Cubical.Foundations.Isomorphism
open import Path
open import Prelude

is-prop : ∀ {ℓ} → Type ℓ → Type ℓ
is-prop A = (p q : A) → p ≡ q

is-type : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
is-type zero = is-prop
is-type (succ n) A = (x y : A) → is-type n (x ≡ y)

record NType ℓ n : Type (lsuc ℓ) where
  field
    ∞-type : Type ℓ
    is-n-type : is-type n ∞-type

open NType public

is-dprop : (I → Type) → Type
is-dprop A = (p : A i0) (q : A i1) → PathP A p q

is-set : ∀ {ℓ} → Type ℓ → Type ℓ
is-set = is-type 1

is-groupoid : ∀ {ℓ} → Type ℓ → Type ℓ
is-groupoid = is-type 2

prop-is-dprop : {A : I → Type} → ((i : I) → is-prop (A i)) → is-dprop A
prop-is-dprop {A} A-prop p = transp (λ t → (q′ : A t) → PathP (λ i → A (t ∧ i)) p q′) i0 (A-prop i0 p)

prop-is-set : ∀ {ℓ} {A : Type ℓ} → is-prop A → is-set A
prop-is-set pr x y p q i j =
  hcomp (λ h → λ { (i = i0) → p j
                 ; (i = i1) → pr (q j) (q j) (~ h)
                 ; (j = i0) → pr x x (i ∧ ~ h)
                 ; (j = i1) → pr y y (i ∧ ~ h) }) (pr (p j) (q j) i)

type-is-succ-type : ∀ {ℓ} (n : ℕ) {A : Type ℓ} → is-type n A → is-type (succ n) A
type-is-succ-type zero = prop-is-set
type-is-succ-type (succ n) pr x y = type-is-succ-type n (pr x y)

set-square : {A : Type} → is-set A → {a b c d : A} → (p : a ≡ b) (q : c ≡ d) (r : a ≡ c) (s : b ≡ d) → PathP (λ i → r i ≡ s i) p q
set-square {A} A-set p q r s i j =
  hcomp (λ h → λ { (i = i0) → p j
                 ; (i = i1) → A-set _ _ (λ j′ → base i1 j′) q h j
                 ; (j = i0) → r i
                 ; (j = i1) → s i }) (base i j)
  where
    base : I → I → A
    base i′ j′ = hfill (λ h → λ { (j′ = i0) → r h
                                ; (j′ = i1) → s h }) (inS (p j′)) i′

is-prop-is-prop : ∀ {ℓ} (A : Type ℓ) → is-prop (is-prop A)
is-prop-is-prop _ α β i x y j =
  hcomp (λ h → λ { (i = i0) → α (α x y j) (α x y j) h
                 ; (i = i1) → α (α x y j) (β x y j) h
                 ; (j = i0) → α x x h
                 ; (j = i1) → α y y h }) (α x y j)

{-
n-type-prop : ∀ {ℓ} n → is-prop (NType ℓ n)
∞-type (n-type-prop zero A B i) = isoToPath φ i
  where
    φ : Iso (∞-type A) (∞-type B)
    Iso.fun φ = {!!}
    Iso.inv φ = {!!}
    Iso.rightInv φ = {!!}
    Iso.leftInv φ = {!!}
is-n-type (n-type-prop zero A B i) = {!!}
n-type-prop (succ n) = {!!}
-}

data ■₀ {ℓ} (A : Type ℓ) : Type ℓ where
  forget₀ : A → ■₀ A
  collapse₀ : is-prop (■₀ A)

from-■₀ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → is-prop B → (A → B) → ■₀ A → B
from-■₀ pr f (forget₀ x) = f x
from-■₀ pr f (collapse₀ x y i) = pr (from-■₀ pr f x) (from-■₀ pr f y) i

_►_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → ■₀ A → (A → B) → ■₀ B
x ► f = from-■₀ collapse₀ (λ y → forget₀ (f y)) x

recall₀ : ∀ {ℓ} {A : Type ℓ} → is-prop A → ■₀ A → A
recall₀ pr = from-■₀ pr (λ x → x)

join : ∀ {ℓ} {A : Type ℓ} → ■₀ (■₀ A) → ■₀ A
join = recall₀ collapse₀

_►►_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → ■₀ A → (A → ■₀ B) → ■₀ B
x ►► f = join (x ► f)
