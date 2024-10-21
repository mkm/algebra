{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Vec where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Data.Nat
open import Data.Fin
open import Data.Int using ()
open import Data.Show renaming (_++_ to _++′_)
open import Data.Truncation.Base

private
  variable
    ℓ ℓ′ : Level
    m n : ℕ
    A : Type ℓ
    B : Type ℓ′

infixr 25 _∷_
data Vec (A : Type ℓ) : ℕ → Type ℓ where
  [] : Vec A zero
  _∷_ : A → Vec A n → Vec A (succ n)

transp-vec : m ≡ n → Vec A m → Vec A n
transp-vec {n = zero} p [] = []
transp-vec {n = succ n} p [] = absurd $ zero-vs-succ p
transp-vec {n = zero} p (x ∷ xs) = absurd $ zero-vs-succ (inv p)
transp-vec {n = succ n} p (x ∷ xs) = x ∷ transp-vec (succ-inj p) xs

transp-vec-refl : ∀ n → transp-vec {A = A} (refl-at n) ≡ id
transp-vec-refl .zero i [] = []
transp-vec-refl (.succ n) i (x ∷ xs) = x ∷ transp-vec-refl n i xs

drop : (k : ℕ) → Vec A n → Vec A (n ∖ k)
drop zero xs = xs
drop {A = A} (succ k) [] = transp-vec (λ i → ∖-zero (succ k) (~ i)) [] 
drop {A = A} {n = .succ n} (succ k) (x ∷ xs) = transp-vec (λ i → ∖-succ n k (~ i)) (drop k xs)

head′ : ∀ {n n′} → n ≡ succ n′ → Vec A n → A
head′ p [] = absurd $ zero-vs-succ p
head′ _ (x ∷ _) = x

head : Vec A (succ n) → A
head = head′ refl

tail : Vec A (succ n) → Vec A n
tail = drop 1

infixl 30 _!!_
_!!_ : Vec A n → Fin n → A
xs !! fzero = head xs
xs !! fsucc k = tail xs !! k

tabulate : (Fin n → A) → Vec A n
tabulate {n = zero} f = []
tabulate {n = succ n} f = f fzero ∷ tabulate (f ∘ fsucc)

infixr 25 _++_
_++_ : Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_++₃_++₃_ : ∀ {m n k} (xs : Vec A m) (ys : Vec A n) (zs : Vec A k) → Path (λ i → Vec A ((m +₃ n +₃ k) i)) ((xs ++ ys) ++ zs) (xs ++ (ys ++ zs))
[] ++₃ ys ++₃ zs = refl
((x ∷ xs) ++₃ ys ++₃ zs) i = x ∷ (xs ++₃ ys ++₃ zs) i

replicate : (n : ℕ) → A → Vec A n
replicate zero _ = []
replicate (succ n) x = x ∷ replicate n x

map-vec : (A → B) → Vec A n → Vec B n
map-vec {n = zero} f _ = []
map-vec {n = succ n} f xs = f (head xs) ∷ map-vec f (tail xs)

map₂-vec : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ} {n} → (A → B → C) → Vec A n → Vec B n → Vec C n
map₂-vec {n = zero} f _ _ = []
map₂-vec {n = succ n} f xs ys = f (head xs) (head ys) ∷ map₂-vec f (tail xs) (tail ys)

map₃-vec : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ} {n} → (A → B → C → D) → Vec A n → Vec B n → Vec C n → Vec D n
map₃-vec {n = zero} f _ _ _ = []
map₃-vec {n = succ n} f xs ys zs = f (head xs) (head ys) (head zs) ∷ map₃-vec f (tail xs) (tail ys) (tail zs)

foldr : ∀ {A : Type ℓ} {B : ℕ → Type ℓ′} → B zero → (∀ {n} → A → B n → B (succ n)) → ∀ {n} → Vec A n → B n
foldr nil cons [] = nil
foldr nil cons (x ∷ xs) = cons x (foldr nil (λ {n} → cons {n}) xs)

count : (A → Bool) → Vec A n → ℕ
count f [] = 0
count f (x ∷ xs) with f x
count f (x ∷ xs) | false = count f xs
count f (x ∷ xs) | true = succ $ count f xs

filter : (f : A → Bool) (xs : Vec A n) → Vec A (count f xs)
filter f [] = []
filter f (x ∷ xs) with f x
filter f (x ∷ xs) | false = filter f xs
filter f (x ∷ xs) | true = x ∷ filter f xs

flatten : ∀ {m n} → Vec (Vec A n) m → Vec A (m · n)
flatten [] = []
flatten {m = .succ m} {n = n} (xs ∷ xss) = transp-vec (λ i → +-comm (m · n) n (~ i)) (xs ++ flatten xss)

rev-append : ∀ {A : Type ℓ} {m n} → Vec A m → Vec A n → Vec A (m +ᵣ n)
rev-append [] ys = ys
rev-append (x ∷ xs) ys = rev-append xs (x ∷ ys)

reverse : ∀ {A : Type ℓ} {n} → Vec A n → Vec A n
reverse {A = A} {n = n} xs = transport (λ i → Vec A (+ᵣ-zero n i)) (rev-append xs [])

{-
rev-rev-append : ∀ {A : Type ℓ} {m n k} (xs : Vec A m) (ys : Vec A n) (zs : Vec A k) → Path (λ i → Vec A (+ᵣ-assoc m n k i)) (rev-append (rev-append xs ys) zs) (rev-append ys (xs ++ zs))
rev-rev-append [] ys zs = {!!}
rev-rev-append (x ∷ xs) ys zs = {!!}
-}

std-vec : ∀ {A : Type ℓ} {n} → Vec A n → Vec A n
std-vec = map-vec id

tabulate-index : ∀ {A : Type ℓ} {n} (xs : Vec A n) → tabulate (λ k → xs !! k) ≡ xs
tabulate-index [] = refl
tabulate-index {n = .succ n} (x ∷ xs) = (λ i → x ∷ tabulate (λ k → transp-vec-refl n i xs !! k)) ■ (λ i → x ∷ tabulate-index xs i)

index-tabulate : ∀ {A : Type ℓ} {n} (f : Fin n → A) (k : Fin n) → tabulate f !! k ≡ f k
index-tabulate f fzero = refl
index-tabulate {n = .succ n} f (fsucc k) = (λ i → transp-vec-refl n i (tabulate (f ∘ fsucc)) !! k) ■ index-tabulate (f ∘ fsucc) k

vec-index-equiv : ∀ (A : Type ℓ) n → Vec A n ≅ (Fin n → A)
fun (vec-index-equiv _ _) = _!!_
linv (is-equiv (vec-index-equiv _ _)) = tabulate
rinv (is-equiv (vec-index-equiv _ _)) = tabulate
is-linv (is-equiv (vec-index-equiv _ _)) i xs = tabulate-index xs i
is-rinv (is-equiv (vec-index-equiv _ _)) i f k = index-tabulate f k i

vec-index-path : ∀ (A : Type ℓ) n → Vec A n ≡ (Fin n → A)
vec-index-path A n = equiv-path (vec-index-equiv A n)

transpose-path : ∀ {A : Type ℓ} m n → Vec (Vec A n) m ≡ Vec (Vec A m) n
transpose-path {A = A} m n i =
  hcomp (∂ i) λ where
    j (i = i0) → vec-index-path (vec-index-path A n (~ j)) m (~ j)
    j (j = i0) → flip-path (Fin m) (Fin n) A i
    j (i = i1) → vec-index-path (vec-index-path A m (~ j)) n (~ j)

transpose : ∀ {A : Type ℓ} {m n} → Vec (Vec A n) m → Vec (Vec A m) n
transpose = transport (transpose-path _ _)

{-
vec-set″ : ∀ {m n} (α : m ≡ n)
  → IsSet A → (xs : Vec A m) (ys : Vec A n) (p q : transp-vec α xs ≡ ys) → p ≡ q
vec-set″ α A-set [] [] p q i j = {! !}
  where
    lemma : ∀ {n₁ n₂} (α₁ : zero ≡ n₁) (α₂ : zero ≡ n₂)
      (pⱼ : Vec A n₁) (qⱼ : Vec A n₂) → transp-vec α₁ [] ≡ pⱼ → transp-vec α₂ [] ≡ qⱼ → transp-vec (inv α₁ ■ α₂) pⱼ ≡ qⱼ
    lemma _ _ [] [] _ _ = refl
    lemma _ _ pⱼ qⱼ _ _ = {! !}
vec-set″ α A-set xs ys p q i j = {! !}

vec-set′ : ∀ {m n} (α : m ≡ n)
  → IsSet A → (xs : Vec A m) (ys : Vec A n) (p q : Path (λ i → Vec A (α i)) xs ys) → p ≡ q
vec-set′ α A-set [] [] p q i j = {! !} -- lemma (λ i → α (i ∧ j)) (λ i → α (i ∧ j)) (p j) (q j) (λ i → p (i ∧ j)) (λ i → q (i ∧ j)) i
  where
    lemma : ∀ {n₁ n₂} (α₁ : zero ≡ n₁) (α₂ : zero ≡ n₂)
      (pⱼ : Vec A n₁) (qⱼ : Vec A n₂)
      → Path (λ i → Vec A (α₁ i)) [] pⱼ → Path (λ i → Vec A (α₂ i)) [] qⱼ → Path (λ i → Vec A (can-path (inv α₁ ■ α₂) i)) pⱼ qⱼ
    lemma α₁ α₂ [] [] _ _ = refl
    lemma α₁ α₂ _ _ p′ q′ = {! !} -- inv p′ ■ q′
vec-set′ α A-set xs ys p q i j = {! !}
-}

{-
vec-set : ∀ {A : Type ℓ} {n} → IsSet A → IsSet (Vec A n)
vec-set A-set [] [] p q i j = lemma (p j) (q j) i
  where
    lemma : ∀ pⱼ qⱼ → pⱼ ≡ qⱼ
    lemma [] [] = refl
vec-set A-set (x ∷ xs) (y ∷ ys) p q = {! !}
-}

{-
instance
  vec-show : ∀ {A : Type ℓ} {n} ⦃ _ : Show A ⦄ → Show (Vec A n)
  show ⦃ vec-show ⦄ [] = "[]"
  show ⦃ vec-show ⦄ (x ∷ xs) = "[" ++′ show x ++′ foldr "]" (λ x s → " , " ++′ show x ++′ s) xs
-}
