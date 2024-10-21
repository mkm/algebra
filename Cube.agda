{-# OPTIONS --cubical --prop #-}
module Cube where

open import Agda.Primitive
open import Path
open import Logic
open import Nat
open import Product

data Cube : ℕ → Type where
  * : Cube 0
  ↓ : ∀ {n} → Cube n → Cube (succ n)
  ↑ : ∀ {n} → Cube n → Cube (succ n)
  c : ∀ {n} (◼ : Cube n) → ↓ ◼ ≡ ↑ ◼

Rim : ℕ → Type

rim : ∀ {n} → Rim n → Cube n

data Cyl (n : ℕ) : Type where
  floor : Cube n → Cyl n
  ceil : Cube n → Cyl n
  wall : ∀ ◻ → floor (rim ◻) ≡ ceil (rim ◻)

Rim zero = ♯ ⊥
Rim (succ n) = Cyl n

rim {succ n} (floor ◼) = ↓ ◼
rim {succ n} (ceil ◼) = ↑ ◼
rim {succ n} (wall ◻ i) = c (rim ◻) i

base : ∀ {n} → Cube n
base {zero} = *
base {succ _} = ↓ base

{-
base-path : ∀ {n} (◼ : Cube n) → base ≡ ◼
base-path * _ = *
base-path (↓ ◼) j = ↓ (base-path ◼ j)
base-path (↑ ◼) j = {!c ◼ j!}
{-
  hcomp (λ h → λ { (j = i0) → ↓ base
                 ; (j = i1) → c ◼ h }) (base-path ◼ j) -}
base-path (c ◼ i) j = {!!}
base-path {n} (c ◼₁ ◼₂ i) j = {!system i0 i0!}
  where
    system : (i j : I) → I → Partial (~ i ∨ i ∨ ~ j) (Cube n)
    system i j h (i = i0) = ↓ (base-path (base-path ◼₁ j) h)
    system i j h (i = i1) = c base ◼₂ j
    system i j h (j = i0) = {!!}

Cube-prop : ∀ {n} → is-prop (Cube n)
Cube-prop ◼₁ ◼₂ = base-path ◼₁ ~∘ base-path ◼₂
-}

get-↓ : ∀ {ℓ} {A : Type ℓ} {n} → (Cube (succ n) → A) → Cube n → A
get-↓ p ◼ = p (↓ ◼)

get-↑ : ∀ {ℓ} {A : Type ℓ} {n} → (Cube (succ n) → A) → Cube n → A
get-↑ p ◼ = p (↑ ◼)

get-← : ∀ {ℓ} {A : Type ℓ} {n} → (Cube (succ (succ n)) → A) → Cube (succ n) → A
get-← p (↓ ◼) = p (↓ (↓ ◼))
get-← p (↑ ◼) = p (↑ (↓ ◼))
get-← p (c ◼ i) = p (c (↓ ◼) i)

get-→ : ∀ {ℓ} {A : Type ℓ} {n} → (Cube (succ (succ n)) → A) → Cube (succ n) → A
get-→ p (↓ ◼) = p (↓ (↑ ◼))
get-→ p (↑ ◼) = p (↑ (↑ ◼))
get-→ p (c ◼ i) = p (c (↑ ◼) i)

cube₀ : ∀ {ℓ} {A : Type ℓ} → A → Cube 0 → A
cube₀ p * = p

cube₁ : ∀ {ℓ} {A : Type ℓ} → (I → A) → Cube 1 → A
cube₁ p (↓ *) = p i0
cube₁ p (↑ *) = p i1
cube₁ p (c * i) = p i

cube₂ : ∀ {ℓ} {A : Type ℓ} → (I → I → A) → Cube 2 → A
cube₂ p (↓ (↓ *)) = p i0 i0
cube₂ p (↓ (↑ *)) = p i0 i1
cube₂ p (↓ (c * j)) = p i0 j
cube₂ p (↑ (↓ *)) = p i1 i0
cube₂ p (↑ (↑ *)) = p i1 i1
cube₂ p (↑ (c * j)) = p i1 j
cube₂ p (c (↓ *) i) = p i i0
cube₂ p (c (↑ *) i) = p i i1
cube₂ p (c (c * j) i) = p i j

uncube₀ : ∀ {ℓ} {A : Type ℓ} → (Cube 0 → A) → A
uncube₀ p = p *

uncube₁ : ∀ {ℓ} {A : Type ℓ} → (p : Cube 1 → A) → uncube₀ (get-↓ p) ≡ uncube₀ (get-↑ p)
uncube₁ p i = p (c * i)

uncube₂ : ∀ {ℓ} {A : Type ℓ} → (p : Cube 2 → A) → uncube₁ (get-↓ p) =⟦ i ⊢ uncube₁ (get-← p) i ≡ uncube₁ (get-→ p) i ⟧= uncube₁ (get-↑ p)
uncube₂ p i j = p (c (c * j) i)

rim₀ : ∀ {ℓ} {A : Type ℓ} → Partial i0 A → Rim 0 → A
rim₀ _ ()

rim₁ : ∀ {ℓ} {A : Type ℓ} → ((i : I) → Partial (~ i ∨ i) A) → Rim 1 → A
rim₁ p (floor *) = p i0 1=1
rim₁ p (ceil *) = p i1 1=1

rim₂ : ∀ {ℓ} {A : Type ℓ} → ((i j : I) → Partial (~ i ∨ i ∨ ~ j ∨ j) A) → Rim 2 → A
rim₂ p (floor ◼) = cube₁ (λ j → p i0 j 1=1) ◼
rim₂ p (ceil ◼) = cube₁ (λ j → p i1 j 1=1) ◼
rim₂ p (wall (floor *) i) = p i i0 1=1
rim₂ p (wall (ceil *) i) = p i i1 1=1

unrim₀ : ∀ {ℓ} {A : Type ℓ} → (r : Rim 0 → A) → Partial i0 A
unrim₀ r ()

unrim₁ : ∀ {ℓ} {A : Type ℓ} → (Rim 1 → A) → (i : I) → Partial (~ i ∨ i) A
unrim₁ r i (i = i0) = r (floor *)
unrim₁ r i (i = i1) = r (ceil *)

unrim₂ : ∀ {ℓ} {A : Type ℓ} → (Rim 2 → A) → (i j : I) → Partial (~ i ∨ i ∨ ~ j ∨ j) A
unrim₂ r i j (i = i0) = r (floor (c * j))
unrim₂ r i j (i = i1) = r (ceil (c * j))
unrim₂ r i j (j = i0) = r (wall (floor *) i)
unrim₂ r i j (j = i1) = r (wall (ceil *) i)

module Test where
  open import Circle

  loop-cube : Cube 1 → S¹
  loop-cube = cube₁ λ i → loop i

{-
Rim : ∀ {n} → Cube n → Type

record Cyl {n} (◼₁ ◼₂ : Cube n) : Type where

Rim * = ♯ ⊥
Rim (↑ ◼) = Rim ◼
Rim (c ◼₁ ◼₂ i) = {!!}
-}

{-
data 𝟐 : Type where
  𝟎 : 𝟐
  𝟏 : 𝟐

Rim : ℕ → Type
Cube : (n : ℕ) → Rim n → Type

data Cyl (n : ℕ) : Type where
  rim : 𝟐 → Rim n → Cyl n
  lid : ∀ {◻} → (ρ : 𝟐) → Cube n (rim ρ ◻) → Cyl n
  wall : rim 𝟎 ≡ rim 𝟏

open Cyl public

Rim zero = ♯ ⊥
Rim (succ n) = Cyl n

Cube (succ n) ◻ = ? -- lids ◻ 𝟎 =⟦ i ⊢ Cube n (walls ◻ i) ⟧= lids ◻ 𝟏
-}

{-
Shell : ∀ {ℓ} → Type ℓ → ℕ → Type ℓ
Cube : ∀ {ℓ} (A : Type ℓ) (n : ℕ) → Shell A n → Type ℓ

record Point {ℓ} : Type ℓ where
  constructor *

record Cylinder {ℓ} (A : Type ℓ) (n : ℕ) : Type ℓ where
  constructor cylinder
  eta-equality
  inductive
  field
    {floorₛ} : Shell A n
    {ceilₛ} : Shell A n
    floor : Cube A n floorₛ
    ceil : Cube A n ceilₛ
    wall : floorₛ ≡ ceilₛ

open Cylinder public

Shell A zero = Point
Shell A (succ n) = Cylinder A n

Cube A zero ◻ = A
Cube A (succ n) ◻ = floor ◻ =⟦ i ⊢ Cube A n (wall ◻ i) ⟧= ceil ◻

id-shell : ∀ {ℓ} {A : Type ℓ} (a : A) (n : ℕ) → Shell A n
id-cube : ∀ {ℓ} {A : Type ℓ} (a : A) (n : ℕ) → Cube A n (id-shell a n)

id-shell a zero = *
id-shell a (succ n) = cylinder (id-cube a n) (id-cube a n) id

id-cube a zero = a
id-cube a (succ n) = id

{-
symₛ : ∀ {ℓ} (A : Type ℓ) (n : ℕ) → Shell A (succ (succ n)) ≡ Shell A (succ (succ n))
sym : ∀ {ℓ} (A : Type ℓ) (n : ℕ) (◻ : Shell A (succ (succ n))) → Cube A (succ (succ n)) ◻ =⟦ i ⊢ Cube A (succ (succ n)) (transp (λ t → symₛ A n (i ∧ t)) (~ i) ◻) ⟧= Cube A (succ (succ n)) (transport (symₛ A n) ◻)

symₛ A n = {!!}
sym A n ◻ = ?
-}

module Test where
  open import Circle

  test : Cube S¹ 2 (cylinder loop id (i ⊢ cylinder (loop i) base id))
  test i j = loop (i ∨ j)
-}

{-
data ⸨_⸩ (A : Type) : Type where
  floor : A → ⸨ A ⸩
  ceil : A → ⸨ A ⸩
  cylinder : (x : A) → floor x ≡ ceil x

Cube : ℕ → Type
Cube zero = ♯ ⊤
Cube (succ n) = ⸨ Cube n ⸩

data Split : ℕ → ℕ → ℕ → Type where
  done : Split zero zero zero
  left : ∀ {m n k} → Split m n k → Split (succ m) n (succ k)
  right : ∀ {m n k} → Split m n k → Split m (succ n) (succ k)

embed : ∀ {m n k} → Split m n k → Cube m → Cube n → Cube k
embed done _ _ = lift top
embed (left s) (floor ◻₁) ◻₂ = floor (embed s ◻₁ ◻₂)
embed (left s) (ceil ◻₁) ◻₂ = ceil (embed s ◻₁ ◻₂)
embed (left s) (cylinder ◻₁ i) ◻₂ = cylinder (embed s ◻₁ ◻₂) i
embed (right s) ◻₁ (floor ◻₂) = floor (embed s ◻₁ ◻₂)
embed (right s) ◻₁ (ceil ◻₂) = ceil (embed s ◻₁ ◻₂)
embed (right s) ◻₁ (cylinder ◻₂ i) = cylinder (embed s ◻₁ ◻₂) i

_≈_ : ∀ {n} {A : Type} → (Cube (succ n) → A) → (Cube (succ n) → A) → Type
_≈_ {n} α β =
  (s : Split 1 n (succ n)) (p : Cube 1) (◻ : Cube n) →
  (α (embed s (floor (lift top)) ◻) ≡ β (embed s (floor (lift top)) ◻)) ×
  (α (embed s (ceil (lift top)) ◻) ≡ β (embed s (ceil (lift top)) ◻))
-}

{-
Box : ℕ → Type

boundary : ∀ {n} → Cube n → Box n

data Box′ (n : ℕ) : Type where
  box-floor : Cube n → Box′ n
  box-ceil : Cube n → Box′ n
  box-cylinder : (◻ : Cube n) → boundary (box-floor ◻) ≡ boundary (box-ceil ◻)

open Box′ public

Box zero = ♯ ⊥
Box (succ n) = Box′ n

boundary {zero} ◻ = {!!}
boundary {succ n} ◻ = {!!}
-}
