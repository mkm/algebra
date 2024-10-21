{-# OPTIONS --cubical --erasure #-}
module Data.Truncation.Base where

open import Prelude
open import Path.Comp
open import Data.SNat
open import Data.IVec

private
  variable
    ℓ : Level

IsProp : Type ℓ → Type ℓ
IsProp A = (x y : A) → x ≡ y

IsNType : ℕ → Type ℓ → Type ℓ
IsNType zero A = IsProp A
IsNType (succ n) A = (x y : A) → IsNType n (x ≡ y)

IsMType : ℕ → Type ℓ → Type ℓ
IsMType zero A = Σ A λ x → ∀ y → x ≡ y
IsMType (succ n) A = (x y : A) → IsMType n (x ≡ y)

IsSet : Type ℓ → Type ℓ
IsSet = IsNType 1

IsGroupoid : Type ℓ → Type ℓ
IsGroupoid = IsNType 2

NType : ℕ → ∀ ℓ → Type (lsuc ℓ)
NType h ℓ = Σ (Type ℓ) (IsNType h)

PropType : ∀ ℓ → Type (lsuc ℓ)
PropType = NType 0

PropType₀ : Type₁
PropType₀ = PropType lzero

SetType : ∀ ℓ → Type (lsuc ℓ)
SetType = NType 1

IsPropₚ : (I → Type ℓ) → Type ℓ
IsPropₚ A = (x : A i0) (y : A i1) → Path (λ i → A i) x y

IsSetₚ : (I → I → Type ℓ) → Type ℓ
IsSetₚ A =
  {a : A i0 i0} {b : A i0 i1} {c : A i1 i0} {d : A i1 i1}
  (p : Path (λ j → A i0 j) a b) (q : Path (λ i → A i i0) a c) (r : Path (λ i → A i i1) b d) (s : Path (λ j → A i1 j) c d)
  → Path (λ i → Path (λ j → A i j) (q i) (r i)) p s

data ∣_∣₀ (A : Type ℓ) : Type ℓ where
  forget₀ : A → ∣ A ∣₀
  collapse₀ : IsProp ∣ A ∣₀

propₚ : (A : I → Type ℓ) → IsProp (A i0) → IsPropₚ A
propₚ A = transport (λ t → IsPropₚ λ i → A (i ∧ t))

dprop : {A B : Type ℓ} (P : A ≡ B) → IsProp A → (x : A) (y : B) → Path′ P x y
dprop P = transport (λ t → ∀ x y → Path (λ i → P (t ∧ i)) x y) 

prop-fill : {A : I → Type ℓ} → (∀ i → IsProp (A i)) → (i : I) → (∀ i → Partial (∂ i) (A i)) → A i
prop-fill {A = A} A-prop i f =
  hcomp (∂ i) λ where
    j (i = i0) → A-prop i0 x (f i0 is-one) j
    j (i = i1) → A-prop i1 x (f i1 is-one) j
    j (j = i0) → x
  where
    x : A i
    x = transport (λ t → A (i ∧ t)) (f i0 is-one)

{-
setₚ : (A : I → I → Type ℓ) → IsSet (A i0 i0) → IsSetₚ A
setₚ A = {! transport (λ t → IsSetₚ λ i j → A (i ∧ t) (j ∧ t))  !}
-}

dset : {A : I → Type ℓ} → (∀ i → IsSet (A i)) → (x : A i0) (y : A i1) (p q : Path A x y) → p ≡ q
dset A-set x y p q i j =
  prop-fill (λ j → A-set j (p j) (q j)) j
    (λ where
      j (j = i0) → λ _ → x
      j (j = i1) → λ _ → y)
    i

set-fill : {A : I → I → Type ℓ} → (∀ i j → IsSet (A i j))
  → (i j : I) → (∀ i j → Partial (∂ i ∨ ∂ j) (A i j)) → A i j
set-fill {A = A} A-set i j f =
  hcomp (∂ i ∨ ∂ j) λ where
    k (j = i0) → f i i0 is-one
    k (i = i0) → f i0 j is-one
    k (i = i1) → f i1 j is-one
    k (j = i1) → dset (λ i → A-set i i1) (f i0 i1 is-one) (f i1 i1 is-one) (λ i → base i i1) (λ i → f i i1 is-one) k i
    k (k = i0) → base i j
  where
    base : (i j : I) → A i j
    base i j =
      fill (λ j → A i j) (∂ i)
        (λ where
          j (i = i0) → f i0 j is-one
          j (j = i0) → f i i0 is-one
          j (i = i1) → f i1 j is-one)
        j

-- dgroupoid : {A : I → I → Type ℓ} → (∀ i j → IsGroupoid (A i j))

{-
groupoid-fill : {A : I → I → I → Type ℓ} → (∀ i j k → IsGroupoid (A i j k))
  → (i j k : I) → (∀ i j k → Partial (∂ i ∨ ∂ j ∨ ∂ k) (A i j k)) → A i j k
groupoid-fill {A = A} A-groupoid i j k f =
  hcomp (∂ i ∨ ∂ j ∨ ∂ k) λ where
    h (k = i0) → f i j i0 is-one
    h (j = i0) → f i i0 k is-one
    h (i = i0) → f i0 j k is-one
    h (i = i1) → f i1 j k is-one
    h (j = i1) → f i i1 k is-one
    h (k = i1) → {! !}
    h (h = i0) → base i j k
  where
    base : ∀ i j k → A i j k
    base i j k =
      fill (λ k → A i j k) (∂ i ∨ ∂ j)
        (λ where
          k (j = i0) → f i i0 k is-one
          k (i = i0) → f i0 j k is-one
          k (i = i1) → f i1 j k is-one
          k (j = i1) → f i i1 k is-one
          k (k = i0) → f i j i0 is-one)
        k
-}

{-
ntype-fill : ∀ {n} {A : IVec I (succₛ n) → Type ℓ} → (∀ js → IsNType (weak-nat n) (A js)) → Cube (succₛ n) A → (js : IVec I (succₛ n)) → A js
ntype-fill {A = A} A-ntype cube (j ∷ js) = {! !}
  where
    sys : ∀ k → Partial (∂ j ∨ boundary js ∨ k ≈ i0) (A (j ∷ js))
    sys k with boundary js
    sys k | b = λ where
      (j = i0) → {! !}
      (j = i1) → {! !}
      (b = i1) → {! !}
      (k = i0) → {! !}
-}

{-
mtype-fill : ∀ {n} {A : IVec I n → Type ℓ} → (∀ js → IsMType (weak-nat n) (A js)) → Cube n A → (js : IVec I n) → A js
mtype-fill A-mtype cube js = {! !}
  where
    sys : ∀ {n} {A : IVec I n → Type ℓ} → Cube n A → (js : IVec I n) (k : I) → Partial (boundary js ∨ k ≈ i0) (A js)
    sys cube [] k (k = i0) = {! !}
    sys cube (j ∷ js) k with boundary js | sys {! !} js k
    sys cube (j ∷ js) k | b | s = λ where
      (j = i0) → {! !}
      (j = i1) → {! !}
      (b = i1) → s is-one
      (k = i0) → {! !}
-}

{-
mtype-fill A-mtype f [] = fst (A-mtype [])
mtype-fill A-mtype f (j ∷ js) =
  hcomp (∂ j) λ where
    k (j = i0) → {! !}
    k (j = i1) → {! !}
    k (k = i0) → {! !}
-}

based-path-prop : {A : Type ℓ} (x : A) → IsProp (BasedPath x)
based-path-prop x α β = inv (contract x α) ■ contract x β

{-
set-fill : {A : I → I → Type ℓ} → (∀ i j → IsSet (A i j)) → (∀ i j → Partial (∂ i ∨ ∂ j) (A i j)) → (i j : I) → A i j
set-fill {A = A} 𝒜 f i j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) →
      prop-fill (λ j → 𝒜 i0 j (x i0 j) (f i0 j is-one))
        (λ where
          j (j = i0) → p i0 i0 is-one
          j (j = i1) → p i0 i1 is-one)
        j k
    k (i = i1) → {!!}
    k (j = i0) → {!!}
    k (j = i1) → {!!}
    k (k = i0) → x i j
  where
    x : ∀ i j → A i j
    x i j = transp (λ t → A (i ∧ t) (j ∧ t)) i0 (f i0 i0 is-one)
    p : ∀ i j → PartialP (∂ i ∨ ∂ j) λ o → x i j ≡ f i j o
    p i j (i = i0) = path λ k → transp (λ t → A i0 (j ∧ (t ∨ k))) (k ≈ i1) (f i0 (j ∧ k) is-one)
    p i j (i = i1) = {!path λ k → transp (λ t → A t (j ∧ (t ∨ k))) (k ≈ i1) (f i0 (j ∧ k) is-one)!}
    p i j (j = i0) = path λ k → transp (λ t → A (i ∧ (t ∨ k)) i0) (k ≈ i1) (f (i ∧ k) i0 is-one)
    p i j (j = i1) = {!!}
-}

{-
set-fill : {A : Type ℓ} → IsSet A → (ϕ i j : I) (x : A) (f : Partial (ϕ ∨ ∂ i ∨ ∂ j) A) → PartialP (ϕ ∨ ∂ i ∨ ∂ j) (λ o → ∣ x ≡ f o ∣₀) → A
set-fill 𝒜 ϕ i j x f p =
  hcomp (ϕ ∨ ∂ i ∨ ∂ j) λ where
    k (ϕ = i1) → {!!}
    k (i = i0) → {!prop-fill (𝒜 x₀ (f is-one)) ϕ j  !} -- prop-fill (𝒜 (unsub x) (unsub x)) ϕ j refl {!!} k
    k (i = i1) → {!prop-fill (𝒜 x₀ (f is-one)) ϕ j !}
    k (j = i0) → {!!}
    k (j = i1) → {!!}
    k (k = i0) → x
-}

{-
prop-fill : {A : I → Type ℓ} → ((i : I) → IsProp (A i)) → (ϕ : I) → (f : (i : I) → Partial (ϕ ∨ ∂ i) (A i)) → (i : I) → A i
prop-fill {A = A} 𝒜 ϕ f i =
  hcomp (ϕ ∨ ∂ i) λ where
    j (ϕ = i1) → {!!} -- 𝒜 (𝒜 (f i0 is-one) (f i1 is-one) i) (f i is-one) j
    j (i = i0) → {!!} -- 𝒜 (f i0 is-one) (f i0 is-one) j
    j (i = i1) → {!!} -- 𝒜 (f i1 is-one) (f i1 is-one) j
    j (j = i0) → {!transport (λ t → (x : A (i ∨ t)) (y : A (i ∧ ~ t)) → Path (λ k → between (i ∨ t) (i ∧ ~ t) (path A) k) x y) !} -- 𝒜 (f i0 is-one) (f i1 is-one) i
-}
