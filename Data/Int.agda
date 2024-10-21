{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Int where

open import Prelude renaming (zero to zero′; succ to succ′)
open import Path.Comp
open import Path.Equiv
open import Data.Bool
open import Data.Nat as Nat
  using (+-zero; ·-zero; zero-vs-succ; ℕ-set)
  renaming (_+_ to _+′_; _·_ to _·′_; _∖_ to _∖′_; _+₃_+₃_ to _+₃′_+₃′_; +-comm to +-comm′; _≟_ to _≟′_; ≟-sound to ≟-sound′; ≟-complete to ≟-complete′; ≟-refl to ≟-refl′; ≟-sound-refl to ≟-sound-refl′; can-path to can-path′)
open import Data.Truncation
open import Data.Show

data ℤ : Type where
  neg : ℕ → ℤ
  pos : ℕ → ℤ
  zero : neg 0 ≡ pos 0

ℤ-rec : ∀ {ℓ} {A : Type ℓ} → (ℕ → A) → A → (ℕ → A) → ℤ → A
ℤ-rec _ z _ (neg zero′) = z
ℤ-rec f _ _ (neg (succ′ n)) = f n
ℤ-rec _ z _ (pos zero′) = z
ℤ-rec _ _ f (pos (succ′ n)) = f n
ℤ-rec _ z _ (zero _) = z

ℤ-ind : ∀ {ℓ} {A : ℤ → Type ℓ} → ((n : ℕ) → A (neg (succ′ n))) → A (neg zero′) → ((n : ℕ) → A (pos (succ′ n))) → (n : ℤ) → A n
ℤ-ind _ z _ (neg zero′) = z
ℤ-ind f _ _ (neg (succ′ n)) = f n
ℤ-ind {A = A} _ z _ (pos zero′) = transport (λ i → A (zero i)) z
ℤ-ind _ _ f (pos (succ′ n)) = f n
ℤ-ind {A = A} _ z _ (zero i) = transp (λ t → A (zero (t ∧ i))) (i ≈ i0) z

ℤ-ind-prop : ∀ {ℓ} {A : ℤ → Type ℓ} (A-prop : (n : ℤ) → IsProp (A n)) → ((n : ℕ) → A (neg n)) → ((n : ℕ) → A (pos n)) → (n : ℤ) → A n
ℤ-ind-prop A-prop f _ (neg n) = f n
ℤ-ind-prop A-prop _ g (pos n) = g n
ℤ-ind-prop {A = A} A-prop f g (zero i) = A-prop (zero i) a b i
  where
    a = transp (λ t → A (zero (i ∧ t))) (i ≈ i0) (f zero′)
    b = transp (λ t → A (zero (i ∨ ~ t))) (i ≈ i1) (g zero′)

is-neg : ℤ → Bool
is-neg (neg _) = true
is-neg (pos zero′) = true
is-neg (pos (succ′ _)) = false
is-neg (zero _) = true

is-pos : ℤ → Bool
is-pos (neg zero′) = true
is-pos (neg (succ′ _)) = false
is-pos (pos _) = true
is-pos (zero _) = true

is-nonzero : ℤ → Bool
is-nonzero = ℤ-rec (const true) false (const true)

neg-succ-vs-pos : ∀ {m n} → neg (succ′ m) ≢ pos n
neg-succ-vs-pos p = false-vs-true λ i → is-pos (p i)

neg-vs-pos-succ : ∀ {m n} → neg m ≢ pos (succ′ n)
neg-vs-pos-succ p = false-vs-true λ i → not $ is-neg (p i)

from-neg : ℤ → ℕ
from-neg (neg n) = n
from-neg (pos _) = 0
from-neg (zero _) = 0

from-pos : ℤ → ℕ
from-pos (neg _) = 0
from-pos (pos n) = n
from-pos (zero _) = 0

abs : ℤ → ℕ
abs (neg n) = n
abs (pos n) = n
abs (zero i) = 0

as-neg : ℤ → ℤ
as-neg (neg n) = neg n
as-neg (pos zero′) = neg zero′
as-neg (pos (succ′ n)) = pos (succ′ n)
as-neg (zero _) = neg zero′

as-pos : ℤ → ℤ
as-pos (neg zero′) = pos zero′
as-pos (neg (succ′ n)) = neg (succ′ n)
as-pos (pos n) = pos n
as-pos (zero _) = pos zero′

as-int : (n : ℤ) → as-neg n ≡ as-pos n
as-int (neg zero′) = zero
as-int (neg (succ′ n)) = refl
as-int (pos zero′) = zero
as-int (pos (succ′ n)) = refl
as-int (zero i) = zero

neg-inj : ∀ {m n} → neg m ≡ neg n → m ≡ n
neg-inj p i = from-neg (p i)

pos-inj : ∀ {m n} → pos m ≡ pos n → m ≡ n
pos-inj p i = from-pos (p i)

zero-inj₁ : ∀ {m n} → neg m ≡ pos n → m ≡ 0
zero-inj₁ p i = from-neg (p i)

zero-inj₂ : ∀ {m n} → neg m ≡ pos n → 0 ≡ n
zero-inj₂ p i = from-pos (p i)

zero-pos-inj : ∀ k {n} → zero k ≡ pos n → 0 ≡ n
zero-pos-inj _ p i = from-pos (p i)

infix 25 _≟_
_≟_ : ℤ → ℤ → Bool
neg m ≟ neg n = m ≟′ n
neg m ≟ pos n = m ≟′ 0 && 0 ≟′ n
neg m ≟ zero j = &&-true (m ≟′ 0) (~ j) 
pos m ≟ neg n = m ≟′ 0 && 0 ≟′ n
pos m ≟ pos n = m ≟′ n
pos m ≟ zero j = &&-true (m ≟′ 0) j
zero _ ≟ neg n = 0 ≟′ n
zero _ ≟ pos n = 0 ≟′ n
zero _ ≟ zero _ = true

≟-sound : ∀ m n → So (m ≟ n) → m ≡ n
≟-sound (neg m) (neg n) = ap neg ∘ ≟-sound′ m n
≟-sound (neg zero′) (pos zero′) _ = zero
≟-sound (neg zero′) (zero j) _ k = zero (j ∧ k)
≟-sound (pos m) (pos n) = ap pos ∘ ≟-sound′ m n
≟-sound (pos zero′) (neg zero′) _ = inv zero
≟-sound (pos zero′) (zero j) _ k = zero (j ∨ ~ k)
≟-sound (zero i) (neg zero′) _ k = zero (i ∧ ~ k)
≟-sound (zero i) (pos zero′) _ k = zero (i ∨ k)
≟-sound (zero i) (zero j) _ k = zero ((i ∧ (j ∨ ~ k)) ∨ (j ∧ (i ∨ k)))

≟-refl : ∀ n → So (n ≟ n)
≟-refl (neg n) = ≟-refl′ n
≟-refl (pos n) = ≟-refl′ n
≟-refl (zero i) = oh

≟-complete : ∀ m n → m ≡ n → So (m ≟ n)
≟-complete m n p = transport (λ i → So (m ≟ p i)) (≟-refl m)

≟-sound-refl : ∀ n → ≟-sound n n (≟-refl n) ≡ refl
≟-sound-refl (neg n) i = ap neg (≟-sound-refl′ n i)
≟-sound-refl (pos n) i = ap pos (≟-sound-refl′ n i)
≟-sound-refl (zero _) _ = refl

≟-sound-complete : ∀ m n (p : m ≡ n) → ≟-sound m n (≟-complete m n p) ≡ p
≟-sound-complete m n p = transport (λ i → ≟-sound m (p i) (transp (λ j → So (m ≟ p (i ∧ j))) (i ≈ i0) (≟-refl m)) ≡ (λ j → p (i ∧ j))) (≟-sound-refl m) 

_≟-≡_ : ∀ m n → So (m ≟ n) ≡ (m ≡ n)
m ≟-≡ n = equiv-path α
  where
    α : So (m ≟ n) ≅ (m ≡ n)
    fun α = ≟-sound _ _
    linv (is-equiv α) = ≟-complete m n
    rinv (is-equiv α) = ≟-complete m n
    is-linv (is-equiv α) i σ = so-prop (≟-complete m n (≟-sound m n σ)) σ i
    is-rinv (is-equiv α) i p = ≟-sound-complete m n p i

ℤ-set : IsSet ℤ
ℤ-set m n = transport (λ i → IsProp ((m ≟-≡ n) i)) so-prop

-- zero-inj : ∀ {m n} (p : neg m ≡ pos n) → inv (zero-inj₁ p) ≡ zero-inj₂ p
-- zero-inj = ?

can-path-neg-neg : ∀ {m n} → neg m ≡ neg n → neg m ≡ neg n
can-path-neg-neg p = ap neg $ can-path′ (neg-inj p)

can-path-pos-pos : ∀ {m n} → pos m ≡ pos n → pos m ≡ pos n
can-path-pos-pos p = ap pos $ can-path′ (pos-inj p)

can-path-neg-pos : ∀ {m n} → neg m ≡ pos n → neg m ≡ pos n
-- can-path-neg-pos p = transport (λ t → neg (from-neg (p (~ t))) ≡ pos (from-pos (p t))) zero
can-path-neg-pos {m = zero′} {n = zero′} p = zero
can-path-neg-pos {m = zero′} {n = succ′ _} p = absurd $ neg-vs-pos-succ p
can-path-neg-pos {m = succ′ _} p = absurd $ neg-succ-vs-pos p

can-path-neg-zero : ∀ {m} → Path (λ i → neg m ≡ zero i → neg m ≡ zero i) can-path-neg-neg can-path-neg-pos
can-path-neg-zero {m = zero′} i p = λ j → zero (i ∧ j)
can-path-neg-zero {m = succ′ _} i p =
  unsub (⊥-hcomp (absurd $ neg-succ-vs-pos (p ■ between i i1 zero)) (∂ i) λ where
    (i = i0) → can-path-neg-neg p
    (i = i1) → absurd $ neg-succ-vs-pos p)
-- can-path-neg-zero : ∀ {m} j → neg m ≡ zero j → neg m ≡ zero j
-- can-path-neg-zero j p = transport (λ t → neg (from-neg (p (~ t))) ≡ between i1 j zero t) zero

{-
can-path : {m n : ℤ} → m ≡ n → m ≡ n
can-path {m = neg m} {n = neg n} p = can-path-neg-neg p
can-path {m = neg m} {n = pos n} p = can-path-neg-pos p
can-path {m = neg m} {n = zero j} p = can-path-neg-zero j p
can-path {m = pos m} {n = neg n} p = inv (can-path-neg-pos (inv p))
can-path {m = pos m} {n = pos n} p = can-path-pos-pos p
can-path {m = pos m} {n = zero j} p = {!!}
can-path {m = zero i} {n = neg n} p = {! inv (can-path-neg-zero i (inv p))!}
can-path {m = zero i} {n = pos n} p = {!!}
can-path {m = zero i} {n = zero j} p = {!!}

neg-path : ∀ {m n} (p : neg m ≡ neg n) → ap (neg ∘ from-neg) p ≡ p
neg-path {m = m} p i j = along (p j) (λ i → p (i ∧ j)) i
  where
    along : (pⱼ : ℤ) → neg m ≡ pⱼ → neg (from-neg pⱼ) ≡ pⱼ
    along (neg _) _ = refl
    along (pos zero′) _ = zero
    along (pos (succ′ _)) α = absurd $ neg-vs-pos-succ α
    along (zero i) _ j = zero (i ∧ j)

neg-ap-inj : ∀ {m n} (p : neg m ≡ neg n) → ap neg (neg-inj p) ≡ p
neg-ap-inj {m = m} p i j = lemma (p j) (λ i → p (i ∧ j)) i
  where
    lemma : (pⱼ : ℤ) → neg m ≡ pⱼ → neg (from-neg pⱼ) ≡ pⱼ
    lemma (neg _) _ = refl
    lemma (pos zero′) _ = zero
    lemma (pos (succ′ _)) α = absurd $ neg-vs-pos-succ α
    lemma (zero i) _ j = zero (i ∧ j)

pos-ap-inj : ∀ {m n} (p : pos m ≡ pos n) → ap pos (pos-inj p) ≡ p
pos-ap-inj {m = m} p i j = lemma (p j) (λ i → p (i ∧ j)) i
  where
    lemma : (pⱼ : ℤ) → pos m ≡ pⱼ → pos (from-pos pⱼ) ≡ pⱼ
    lemma (neg zero′) α = inv zero
    lemma (neg (succ′ _)) α = absurd $ neg-succ-vs-pos (inv α)
    lemma (pos _) _ = refl
    lemma (zero i) _ j = zero (i ∨ ~ j) 

zero-ap-inj₁ : ∀ k {n} (p : zero k ≡ pos n) → Path (λ i → zero (i ∧ k) ≡ pos (zero-pos-inj k p i)) zero p
zero-ap-inj₁ k {n = n} p i j = along (zero j) (p j) (between i0 j zero) (between j i1 zero) (between i0 j p) (between j i1 p) i
  where
    along : (zeroⱼ pⱼ : ℤ) → neg 0 ≡ zeroⱼ → zeroⱼ ≡ pos 0 → zero k ≡ pⱼ → pⱼ ≡ pos n → zeroⱼ ≡ pⱼ
    along (neg _) (neg _) zero₀ⱼ zeroⱼ₁ p₀ⱼ pⱼ₀ = {!!}
    along (neg _) (pos _) zero₀ⱼ zeroⱼ₁ p₀ⱼ pⱼ₀ = {!!}
    along (neg _) (zero j′) zero₀ⱼ zeroⱼ₁ p₀ⱼ pⱼ₀ = {!!}
    along (pos _) pⱼ zero₀ⱼ zeroⱼ₁ p₀ⱼ pⱼ₀ = {!!}
    along (zero j) (neg _) zero₀ⱼ zeroⱼ₁ p₀ⱼ pⱼ₀ = {!!}
    along (zero j) (pos _) zero₀ⱼ zeroⱼ₁ p₀ⱼ pⱼ₀ = λ i → as-int (pos (zero-pos-inj k p₀ⱼ i)) (i ∨ j)
    along (zero j) (zero j′) zero₀ⱼ zeroⱼ₁ p₀ⱼ pⱼ₀ = {!!}

zero-ap-inj : ∀ {m n} (p : neg m ≡ pos n) → Path (λ i → neg (zero-inj₁ p (~ i)) ≡ pos (zero-inj₂ p i)) zero p
zero-ap-inj {m = m} {n = n} p i j = lemma (zero j) (p j) (λ i → zero (i ∧ j)) (λ i → zero (i ∨ j)) (λ i → p (i ∧ j)) (λ i → p (i ∨ j)) i
  where
    lemma : (zeroⱼ pⱼ : ℤ) → neg 0 ≡ zeroⱼ → zeroⱼ ≡ pos 0 → neg m ≡ pⱼ → pⱼ ≡ pos n → zeroⱼ ≡ pⱼ
    lemma (neg zero′) (neg pⱼ) α β γ δ = λ t → neg (zero-inj₁ δ (~ t))
    lemma (neg (succ′ _)) (neg _) α β γ δ = absurd $ neg-succ-vs-pos β
    lemma (neg zero′) (pos pⱼ) α β γ δ = λ t → as-int (pos (zero-inj₂ γ t)) t
    lemma (neg (succ′ _)) (pos _) α β γ δ = absurd $ neg-succ-vs-pos β
    lemma (neg zero′) (zero j′) α β γ δ = {!!}
    lemma (neg (succ′ _)) (zero _) α β γ δ = absurd $ neg-succ-vs-pos β
    lemma (pos zero₁) pⱼ α β γ δ = {!!}
    lemma (zero j) (neg pⱼ) α β γ δ = {!!}
    lemma (zero j) (pos pⱼ) α β γ δ = {!!}
    lemma (zero j) (zero j′) α β γ δ = {!!}
{-
lemma (p j) (λ i → p (i ∧ j)) (λ i → p (i ∨ j)) i
  where
    lemma : (pⱼ : ℤ) → neg m ≡ pⱼ → pⱼ ≡ pos n → zero j ≡ pⱼ
    lemma (neg pⱼ) α β i = {!inv (zero-inj₁ p)!}
    lemma (pos pⱼ) α β = {!!}
    lemma (zero k) α β = {!!}
    -}
    {-
    lemma (neg zero′) α β = ? -- λ j → zero (i ∧ ~ j)
    lemma (neg (succ′ _)) α β = absurd $ neg-succ-vs-pos β
    lemma (pos zero′) α β = ? -- λ j → zero (i ∨ j)
    lemma (pos (succ′ _)) α β = absurd $ neg-vs-pos-succ α
    lemma (zero j) α β = {!!}
    -}

ℤ-set : IsSet ℤ
ℤ-set (neg m) (neg n) p q i =
  hcomp (∂ i) λ where
    j (i = i0) → neg-path p j
    j (j = i0) → ap neg (ℕ-set m n (ap from-neg p) (ap from-neg q) i)
    j (i = i1) → neg-path q j
ℤ-set (neg m) (pos n) p q i =
  {!!}
    {-
ℤ-set (neg zero′) (pos zero′) p q i j = lemma (p j) (q j) (λ i → p (i ∧ j)) (λ i → q (i ∧ j)) i
  where
    lemma : ∀ pⱼ qⱼ → neg zero′ ≡ pⱼ → neg zero′ ≡ qⱼ → pⱼ ≡ qⱼ
    lemma (neg zero′) (neg zero′) α β = refl
    lemma (neg zero′) (neg (succ′ _)) α β = β
    lemma (neg (succ′ _)) (neg qⱼ) α β = absurd $ zero-vs-succ (neg-inj α)
    lemma (neg zero′) (pos zero′) α β = zero
    lemma (neg zero′) (pos (succ′ _)) α β = β
    lemma (neg (succ′ _)) (pos zero′) α β = absurd $ zero-vs-succ (neg-inj α)
    lemma (neg (succ′ _)) (pos (succ′ _)) α β = absurd $ neg-vs-pos-succ β
    lemma (neg zero′) (zero j) α β k = zero (j ∧ k)
    lemma (neg (succ′ _)) (zero _) α β = absurd $ zero-vs-succ (neg-inj α)
    lemma (pos zero′) (neg zero′) α β = inv zero
    lemma (pos zero′) (neg (succ′ _)) α β = absurd $ zero-vs-succ (neg-inj β)
    lemma (pos (succ′ _)) (neg zero′) α β = absurd $ neg-vs-pos-succ α
    lemma (pos (succ′ _)) (neg (succ′ _)) α β = absurd $ neg-vs-pos-succ α
    lemma (pos zero′) (pos zero′) α β = refl
    lemma (pos zero′) (pos (succ′ _)) α β = {!!}
    lemma (pos (succ′ _)) (pos zero′) α β = {!!}
    lemma (pos (succ′ _)) (pos (succ′ _)) α β = {!!}
    lemma (pos pⱼ) (zero i) α β = {!!}
    lemma (zero i) qⱼ α β = {!!}
ℤ-set (neg zero′) (pos (succ′ n)) p q = absurd $ neg-vs-pos-succ p
ℤ-set (neg (succ′ m)) (pos n) p q = absurd $ neg-succ-vs-pos p
-}
ℤ-set (neg m) (zero j) p q = {!!}
ℤ-set (pos m) n p q = {!!}
ℤ-set (zero i) n p q = {!!}
-}

negate : ℤ → ℤ
negate (neg n) = pos n
negate (pos n) = neg n
negate (zero i) = zero (~ i)

succ : ℤ → ℤ
succ (neg 0) = pos 1
succ (neg (succ′ n)) = neg n
succ (pos n) = pos (succ′ n)
succ (zero _) = pos 1

pred : ℤ → ℤ
pred (neg n) = neg (succ′ n)
pred (pos 0) = neg 1
pred (pos (succ′ n)) = pos n
pred (zero _) = neg 1

_∖_ : ℕ → ℕ → ℤ
zero′ ∖ n = neg n
m@(succ′ _) ∖ zero′ = pos m
succ′ m ∖ succ′ n = m ∖ n

∖-zero₂ : ∀ m → m ∖ 0 ≡ pos m
∖-zero₂ zero′ = zero
∖-zero₂ (succ′ m) = refl

_+_ : ℤ → ℤ → ℤ
neg m + neg n = neg (m +′ n)
neg m + pos n = n ∖ m
neg m + zero j = neg (+-zero m j)
pos m + neg n = m ∖ n
pos m + pos n = pos (m +′ n)
pos zero′ + zero j = zero j
pos (succ′ m) + zero j = pos (succ′ (+-zero m (~ j)))
zero i + neg n = neg n
zero i + pos zero′ = zero i
zero i + pos (succ′ n) = pos (succ′ n)
zero i + zero j = zero (i ∧ j)

_·_ : ℤ → ℤ → ℤ
neg m · neg n = pos (m ·′ n)
neg m · pos n = neg (m ·′ n)
neg m · zero j =
  hcomp (∂ j) λ where
    k (j = i0) → pos (·-zero m (~ k))
    k (k = i0) → zero (~ j)
    k (j = i1) → neg (·-zero m (~ k))
pos m · neg n = neg (m ·′ n)
pos m · pos n = pos (m ·′ n)
pos m · zero j =
  hcomp (∂ j) λ where
    k (j = i0) → neg (·-zero m (~ k))
    k (k = i0) → zero j
    k (j = i1) → pos (·-zero m (~ k))
zero i · neg n = zero (~ i)
zero i · pos n = zero i
zero i · zero j =
  fill-set-square ℤ-set
    (inv zero)
    (λ j → hcomp (∂ j) λ where
      k (j = i0) → pos 0
      k (k = i0) → zero (~ j)
      k (j = i1) → neg 0)
    (λ j → hcomp (∂ j) λ where
      k (j = i0) → neg 0
      k (k = i0) → zero j
      k (j = i1) → pos 0)
    zero
    i j

_⊕_ : ℤ → ℤ → ℤ
neg m ⊕ n = iterate m pred n
pos m ⊕ n = iterate m succ n
zero _ ⊕ n = n

+-zero₁ : ∀ i n → zero i + n ≡ n
+-zero₁ i (neg n) = refl
+-zero₁ i (pos zero′) j = zero (i ∨ j)
+-zero₁ i (pos (succ′ n)) = refl
+-zero₁ i (zero j) k = zero (j ∧ (i ∨ k))

∖-succ₁ : ∀ m n → succ (m ∖ n) ≡ succ′ m ∖ n
∖-succ₁ zero′ zero′ = refl
∖-succ₁ zero′ (succ′ n) = refl
∖-succ₁ (succ′ m) zero′ = refl
∖-succ₁ (succ′ m) (succ′ n) = ∖-succ₁ m n

∖-pred₁ : ∀ m n → pred (m ∖ n) ≡ m ∖ succ′ n
∖-pred₁ zero′ zero′ = refl
∖-pred₁ zero′ (succ′ n) = refl
∖-pred₁ (succ′ m) zero′ = inv (∖-zero₂ m)
∖-pred₁ (succ′ m) (succ′ n) = ∖-pred₁ m n

+-succ₁ : ∀ m n → succ (m + n) ≡ succ m + n
+-succ₁ = ℤ-ind
  (λ m → ℤ-ind (λ _ → refl) refl (λ n → ∖-succ₁ n m))
  (ℤ-ind (λ _ → refl) refl (λ _ → refl))
  (λ m → ℤ-ind (λ n → ∖-succ₁ m n) refl (λ _ → refl))

+-pred₁ : ∀ m n → pred (m + n) ≡ pred m + n
+-pred₁ (neg zero′) (neg zero′) = refl
+-pred₁ (neg zero′) (neg (succ′ n)) = refl
+-pred₁ (neg (succ′ m)) (neg n) = refl
+-pred₁ (neg zero′) (pos zero′) = refl
+-pred₁ (neg zero′) (pos (succ′ n)) = inv (∖-zero₂ n)
+-pred₁ (neg (succ′ m)) (pos zero′) = refl
+-pred₁ (neg (succ′ m)) (pos (succ′ n)) = ∖-pred₁ n m
+-pred₁ (neg zero′) (zero j) = refl
+-pred₁ (neg (succ′ m)) (zero j) = refl
+-pred₁ (pos zero′) (neg zero′) = refl
+-pred₁ (pos zero′) (neg (succ′ n)) = refl
+-pred₁ (pos (succ′ m)) (neg zero′) = inv (∖-zero₂ m)
+-pred₁ (pos (succ′ m)) (neg (succ′ n)) = ∖-pred₁ m n
+-pred₁ (pos zero′) (pos zero′) = refl
+-pred₁ (pos zero′) (pos (succ′ n)) = inv (∖-zero₂ n)
+-pred₁ (pos (succ′ m)) (pos zero′) = refl
+-pred₁ (pos (succ′ m)) (pos (succ′ n)) = refl
+-pred₁ (pos zero′) (zero j) = refl
+-pred₁ (pos (succ′ m)) (zero j) k = fill-set-square ℤ-set (λ j → pos (+-zero m (~ j))) (inv (∖-zero₂ m)) refl (λ j → pos m + zero j) j k
+-pred₁ (zero i) (neg zero′) = refl
+-pred₁ (zero i) (neg (succ′ n)) = refl
+-pred₁ (zero i) (pos zero′) = refl
+-pred₁ (zero i) (pos (succ′ n)) = inv (∖-zero₂ n)
+-pred₁ (zero i) (zero j) = refl

+-iter-pred₁ : ∀ k m n → iterate k pred (m + n) ≡ iterate k pred m + n
+-iter-pred₁ zero′ m n = refl
+-iter-pred₁ (succ′ k) m n = ap pred (+-iter-pred₁ k m n) ■ +-pred₁ (iterate k pred m) n

+-iter-succ₁ : ∀ k m n → iterate k succ (m + n) ≡ iterate k succ m + n
+-iter-succ₁ zero′ m n = refl
+-iter-succ₁ (succ′ k) m n = ap succ (+-iter-succ₁ k m n) ■ +-succ₁ (iterate k succ m) n

add-neg : ∀ m n → neg m + n ≡ iterate m pred n
add-neg zero′ n = +-zero₁ i0 n
add-neg (succ′ m) n = inv (+-pred₁ (neg m) n) ■ ap pred (add-neg m n)

add-pos : ∀ m n → pos m + n ≡ iterate m succ n
add-pos zero′ n = +-zero₁ i1 n
add-pos (succ′ m) n = inv (+-succ₁ (pos m) n) ■ ap succ (add-pos m n)

add : ∀ m n → m + n ≡ m ⊕ n
add (neg m) n = add-neg m n
add (pos m) n = add-pos m n
add (zero i) n = +-zero₁ i n

+-comm-neg : ∀ x y → neg x + y ≡ y + neg x
+-comm-neg x (neg y) = ap neg (+-comm′ x y)
+-comm-neg x (pos y) = refl
+-comm-neg x (zero i) j = fill-set-square ℤ-set (ap neg (+-zero x)) (ap neg (+-comm′ x 0)) refl refl i j

+-comm-pos : ∀ x y → pos x + y ≡ y + pos x
+-comm-pos x (neg y) = refl
+-comm-pos x (pos y) = ap pos (+-comm′ x y)
+-comm-pos x (zero i) j = fill-set-square ℤ-set (λ i → pos x + zero i) refl (ap pos (+-comm′ x 0)) (λ i → zero i + pos x) i j

+-comm : ∀ x y → x + y ≡ y + x
+-comm = ℤ-ind-prop (λ x → pi-prop λ y → ℤ-set (x + y) (y + x)) +-comm-neg +-comm-pos

⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
⊕-assoc (neg x) y z = transport (λ i → add (iterate x pred y) z i ≡ iterate x pred (add y z i)) (inv (+-iter-pred₁ x y z))
⊕-assoc (pos x) y z = transport (λ i → add (iterate x succ y) z i ≡ iterate x succ (add y z i)) (inv (+-iter-succ₁ x y z))
⊕-assoc (zero i) y z = transport (λ i → add y z i ≡ add y z i) refl

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc = transport (λ i → ∀ x y z → add (add x y (~ i)) z (~ i) ≡ add x (add y z (~ i)) (~ i)) ⊕-assoc

∖-same : ∀ n i → n ∖ n ≡ zero i
∖-same zero′ i j = zero (i ∧ j)
∖-same (succ′ n) i = ∖-same n i

+-negate₁ : ∀ n i → negate n + n ≡ zero i
+-negate₁ (neg n) i = ∖-same n i
+-negate₁ (pos n) i = ∖-same n i
+-negate₁ (zero j) i k = zero ((i ∧ k) ∨ (j ∧ ~ j ∧ ~ k))

+-negate₂ : ∀ n i → n + negate n ≡ zero i
+-negate₂ (neg n) i = ∖-same n i
+-negate₂ (pos n) i = ∖-same n i
+-negate₂ (zero j) i k = zero ((i ∧ k) ∨ (j ∧ ~ j ∧ ~ k))

·-comm : ∀ x y → x · y ≡ y · x
·-comm = ℤ-ind
  (λ x → ℤ-ind
    (λ y i → pos (Nat.·-comm (succ′ x) (succ′ y) i))
    (λ i → pos (Nat.·-comm (succ′ x) zero′ i))
    (λ y i → neg (Nat.·-comm (succ′ x) (succ′ y) i)))
  (ℤ-ind
    (λ y i → pos (Nat.·-comm zero′ (succ′ y) i))
    (λ i → pos zero′)
    (λ y i → neg (Nat.·-comm zero′ (succ′ y) i)))
  (λ x → ℤ-ind
    (λ y i → neg (Nat.·-comm (succ′ x) (succ′ y) i))
    (λ i → neg (Nat.·-comm (succ′ x) zero′ i))
    (λ y i → pos (Nat.·-comm (succ′ x) (succ′ y) i)))

succ-is-equiv : IsEquiv succ
linv succ-is-equiv = pred
rinv succ-is-equiv = pred
is-linv succ-is-equiv i (neg zero′) = zero (~ i)
is-linv succ-is-equiv _ (neg (succ′ n)) = neg (succ′ n)
is-linv succ-is-equiv _ (pos n) = pos n
is-linv succ-is-equiv i (zero j) = zero (~ i ∨ j)
is-rinv succ-is-equiv _ (neg n) = neg n
is-rinv succ-is-equiv i (pos zero′) = zero i
is-rinv succ-is-equiv _ (pos (succ′ n)) = pos (succ′ n)
is-rinv succ-is-equiv i (zero j) = zero (i ∧ j)

succ-equiv : ℤ ≅ ℤ
fun succ-equiv = succ
is-equiv succ-equiv = succ-is-equiv

succ-path : ℤ ≡ ℤ
succ-path = equiv-path succ-equiv

from-succ-path : ∀ i → succ-path i → ℤ
from-succ-path = from-equiv-path succ-equiv

+-is-equiv : ∀ m → IsEquiv (λ n → m + n)
linv (+-is-equiv m) n = negate m + n
rinv (+-is-equiv m) n = negate m + n
is-linv (+-is-equiv m) i n =
  hcomp (∂ i) λ where
    j (i = i0) → +-assoc (negate m) m n j
    j (j = i0) → +-negate₁ m i0 i + n
    j (i = i1) → +-zero₁ i0 n j
is-rinv (+-is-equiv m) i n =
  hcomp (∂ i) λ where
    j (i = i0) → +-assoc m (negate m) n j
    j (j = i0) → +-negate₂ m i0 i + n
    j (i = i1) → +-zero₁ i0 n j

+-equiv : ℤ → ℤ ≅ ℤ
fun (+-equiv m) n = m + n
is-equiv (+-equiv m) = +-is-equiv m

+-path : ℤ → ℤ ≡ ℤ
+-path = equiv-path ∘ +-equiv

private
  data ℤ′ : Type where
    pos′ : ℕ → ℤ′
    negsuc′ : ℕ → ℤ′

  {-# BUILTIN INTEGER ℤ′ #-}
  {-# BUILTIN INTEGERPOS pos′ #-}
  {-# BUILTIN INTEGERNEGSUC negsuc′ #-}

  primitive
    primShowInteger : ℤ′ → String

  int : ℤ → ℤ′
  int (neg zero′) = pos′ zero′
  int (neg (succ′ n)) = negsuc′ n
  int (pos n) = pos′ n
  int (zero _) = pos′ zero′

instance
  ℕ-show : Show ℕ
  show ⦃ ℕ-show ⦄ = primShowInteger ∘ int ∘ pos
  next ⦃ ℕ-show ⦄ = show-refl

  ℤ-show : Show ℤ
  show ⦃ ℤ-show ⦄ = primShowInteger ∘ int
  next ⦃ ℤ-show ⦄ = show-refl
