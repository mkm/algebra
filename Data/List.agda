{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.List where

open import Prelude
open import Path.Comp
open import Data.Truncation.Base
open import Data.Bool

private
  variable
    ℓ ℓ′ : Level
    A : Type ℓ
    B : Type ℓ′

data List (A : Type ℓ) : Type ℓ where
  [] : List A
  _∷_ : A → List A → List A

infixr 40 _∷_

foldr : B → (A → B → B) → List A → B
foldr k _ [] = k
foldr k f (x ∷ xs) = f x (foldr k f xs)

foldrₚ : {B : List A → Type ℓ′} → B [] → ((x : A) {xs : List A} → B xs → B (x ∷ xs)) → (xs : List A) → B xs
foldrₚ k _ [] = k
foldrₚ k f (x ∷ xs) = f x (foldrₚ k f xs)

foldl : B → (B → A → B) → List A → B
foldl k _ [] = k
foldl k f (x ∷ xs) = foldl (f k x) f xs

length : List A → ℕ
length = foldr zero (const succ)

_++_ : List A → List A → List A
xs ++ ys = foldr ys _∷_ xs

infixr 40 _++_

++-[] : (xs : List A) → xs ++ [] ≡ xs
++-[] [] _ = []
++-[] (x ∷ xs) i = x ∷ ++-[] xs i

reverse : List A → List A
reverse = foldl [] (flip _∷_)

replicate : ℕ → A → List A
replicate zero _ = []
replicate (succ n) x = x ∷ replicate n x

head : A → List A → A
head x [] = x
head _ (x ∷ _) = x

tail : List A → List A
tail [] = []
tail (_ ∷ xs) = xs

empty : List A → Bool
empty [] = true
empty (_ ∷ _) = false

[]-vs-∷ : {x : A} {xs : List A} → [] ≢ x ∷ xs
[]-vs-∷ p = false-vs-true λ i → not $ empty (p i)

∷-inj₁ : {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷-inj₁ {x = x} p i = head x (p i)

∷-inj₂ : {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷-inj₂ p i = tail (p i)

∷-ap-inj : {x y : A} {xs ys : List A} (p : x ∷ xs ≡ y ∷ ys) → ap₂ _∷_ (∷-inj₁ p) (∷-inj₂ p) ≡ p
∷-ap-inj {A = A} {x = x} {xs = xs} p i j = lemma (p j) (λ i → p (i ∧ j)) i
  where
    lemma : (pⱼ : List A) → x ∷ xs ≡ pⱼ → head x pⱼ ∷ tail pⱼ ≡ pⱼ
    lemma [] α = absurd $ []-vs-∷ (inv α)
    lemma (pⱼ ∷ psⱼ) α = refl

list-set : IsSet A → IsSet (List A)
list-set A-set [] [] p q i j = lemma (p j) (q j) (λ i → p (i ∧ j)) (λ i → q (i ∧ j)) i
  where
    lemma : ∀ pⱼ qⱼ → [] ≡ pⱼ → [] ≡ qⱼ → pⱼ ≡ qⱼ
    lemma [] [] p′ q′ = refl
    lemma pⱼ qⱼ p′ q′ = inv p′ ■ q′
list-set A-set [] (y ∷ ys) p q = absurd $ []-vs-∷ p
list-set A-set (x ∷ xs) [] p q = absurd $ []-vs-∷ (inv p)
list-set A-set (x ∷ xs) (y ∷ ys) p q i =
  hcomp (∂ i) λ where
    j (i = i0) → ∷-ap-inj p j
    j (j = i0) → ap₂ _∷_ (A-set x y (∷-inj₁ p) (∷-inj₁ q) i) (list-set A-set xs ys (∷-inj₂ p) (∷-inj₂ q) i)
    j (i = i1) → ∷-ap-inj q j
