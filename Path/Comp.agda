{-# OPTIONS --cubical --erasure #-}
module Path.Comp where

open import Prelude
open import Data.SNat
open import Data.IVec

private
  variable
    ℓ : Level
    ℓ₁ ℓ₂ ℓ₃ : Level

Path′ : {A B : Type ℓ} → A ≡ B → A → B → Type ℓ
Path′ P = Path λ i → P i

Pathₖ : (A : Type ℓ) → A → A → Type ℓ
Pathₖ A = Path λ _ → A

Square : {A : Type ℓ} {ul ur ll lr : A} → ul ≡ ur → ul ≡ ll → ur ≡ lr → ll ≡ lr → Type ℓ
Square p q r s = Path (λ i → p i ≡ s i) q r

syntax Square p q r s =
  ┌ p ┐
  q · r
  └ s ┘

SquareP : {UL UR LL LR : Type ℓ} {P : UL ≡ UR} {Q : UL ≡ LL} {R : UR ≡ LR} {S : LL ≡ LR}
  (α : Square P Q R S)
  {ul : UL} {ur : UR} {ll : LL} {lr : LR} (p : Path′ P ul ur) (q : Path′ Q ul ll) (r : Path′ R ur lr) (s : Path′ S ll lr)
   → Type ℓ
SquareP α p q r s = Path (λ i → Path (λ j → α i j) (p i) (s i)) q r

boundary : ∀ {n} → IVec n → I
boundary js = ifoldr i0 _∨_ (imap ∂ js)

HCube : ℕₛ → Type ℓ → SSet ℓ
HCube n A = (js : IVec n) → Partial (boundary js) A

Cube : (n : ℕₛ) → (IVec n → Type ℓ) → SSet ℓ
Cube n A = (js : IVec n) → Partial (boundary js) (A js)

{-
Cube : {A : Type ℓ} → (∀ i j k → Partial (∂ i ∨ ∂ j ∨ ∂ k) A) → Type ℓ
Cube f = Path (λ i → Path (λ j → f i j i0 is-one ≡ f i j i1 is-one) (λ k → f i i0 k is-one) (λ k → f i i1 k is-one)) (λ j k → f i0 j k is-one) (λ j k → f i1 j k is-one)
-}

hfill : {A : Type ℓ} (φ : I) → ((t : I) → Partial (φ ≈ i1 ∨ t ≈ i0) A) → I → A
hfill φ cube h =
  hcomp (φ ≈ i1 ∨ h ≈ i0) λ where
    t (φ = i1) → cube (t ∧ h) is-one
    t (h = i0) → cube i0 is-one
    t (t = i0) → cube i0 is-one

fill : {ℓ : I → Level} (A : (t : I) → Type (ℓ t)) (φ : I) → ((t : I) → Partial (φ ≈ i1 ∨ t ≈ i0) (A t)) → (h : I) → A h
fill A φ cube h =
  comp (λ t → A (t ∧ h)) (φ ≈ i1 ∨ h ≈ i0) λ where
    t (φ = i1) → cube (t ∧ h) is-one
    t (h = i0) → cube i0 is-one
    t (t = i0) → cube i0 is-one

compp : (ℓ : I → Level) (φ : I) (A : (t : I) → Partial (φ ≈ i1 ∨ t ≈ i0) (Type (ℓ t)))
  → ((t : I) → PartialP (φ ≈ i1 ∨ t ≈ i0) (A t))
  → comp (λ t → Type (ℓ t)) φ A
compp ℓ φ A cube =
  comp (fill (λ h → Type (ℓ h)) φ A) φ λ where
    t (φ = i1) → cube t is-one
    t (t = i0) → cube t is-one

transport : {A B : Type ℓ} → A ≡ B → A → B
transport p = transp (λ i → p i) i0

transpot : {A : Type ℓ} → A → A
transpot {A = A} = transport (λ _ → A)

path : {A : I → Type ℓ} (p : (i : I) → A i) → Path A (p i0) (p i1)
path p i = p i

infix 1 _►_
_►_ : {A : Type ℓ} {x y : A} (i : I) → x ≡ y → A
i ► p = p i

between : {A : Type ℓ} {x y : A} (j0 j1 : I) (p : x ≡ y) → p j0 ≡ p j1
between j0 j1 p i = p ((i ∨ j0) ∧ (~ i ∨ j1))

ap : {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f p i = f (p i)

ap₂ : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : A → B → C) {x x′ : A} {y y′ : B} → x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
ap₂ f p q i = f (p i) (q i)

apₚ : {A : Type ℓ₁} {B : A → Type ℓ₂} (f : (x : A) → B x) {x y : A} (p : x ≡ y) → Path (λ i → B (p i)) (f x) (f y)
apₚ f p i = f (p i)

refl-at : {A : Type ℓ} (x : A) → x ≡ x
refl-at x _ = x

instance
  refl : {A : Type ℓ} {x : A} → x ≡ x
  refl = refl-at _

inv : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
inv p i = p (~ i)

ap-hcomp : {A : Type ℓ₁} {B : Type ℓ₂} (ϕ : I) (f : A → B) (g : (t : I) → Partial (ϕ ∨ t ≈ i0) A) → f (hcomp ϕ g) ≡ hcomp ϕ (λ t o → f $ g t o)
ap-hcomp ϕ f g i =
  hcomp (ϕ ∨ i ≈ i0) λ where
    j (ϕ = i1) → f $ g j is-one
    j (i = i0) → f $ hfill ϕ g j
    j (j = i0) → f $ g i0 is-one

diag : {A : Type ℓ} {ul ur ll lr : A} {p : ul ≡ ur} {q : ul ≡ ll} {r : ur ≡ lr} {s : ll ≡ lr}
  → Square p q r s → ul ≡ lr
diag α i = α i i

■-square : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → ┌ p ┐
    p · q
    └ q ┘
■-square {x = x} {y = y} {z = z} p q i j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p (j ∨ ~ k)
    k (j = i0) → p (i ∨ ~ k)
    k (i = i1) → q (j ∧ k)
    k (j = i1) → q (i ∧ k)
    k (k = i0) → y

infixr 30 _■_
_■_ : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(p ■ q) i = ■-square p q i i

■ₚ-square : {A B C : Type ℓ} {P : A ≡ B} {Q : B ≡ C} {x : A} {y : B} {z : C}
  (p : Path′ P x y) (q : Path′ Q y z) → Path (λ i → Path (λ j → ■-square P Q i j) (p i) (q i)) p q
■ₚ-square {ℓ = ℓ} {B = B} {P = P} {Q = Q} {x = x} {y = y} {z = z} p q i j =
  compp (λ _ → ℓ)
    (∂ i ∨ ∂ j)
    (λ where
      k (i = i0) → P (j ∨ ~ k)
      k (j = i0) → P (i ∨ ~ k)
      k (i = i1) → Q (j ∧ k)
      k (j = i1) → Q (i ∧ k)
      k (k = i0) → B)
    (λ where
      k (i = i0) → p (j ∨ ~ k)
      k (j = i0) → p (i ∨ ~ k)
      k (i = i1) → q (j ∧ k)
      k (j = i1) → q (i ∧ k)
      k (k = i0) → y)

infixr 30 _■ₚ_
_■ₚ_ : {A B C : Type ℓ} {P : A ≡ B} {Q : B ≡ C} {x : A} {y : B} {z : C}
  → Path′ P x y → Path′ Q y z → Path′ (P ■ Q) x z
(p ■ₚ q) i = ■ₚ-square p q i i

_■₃_■₃_ : {A : Type ℓ} {x y z w : A} → x ≡ y → y ≡ z → z ≡ w → x ≡ w
(p ■₃ q ■₃ r) i =
  hcomp (∂ i) λ where
    j (i = i0) → p (~ j)
    j (j = i0) → q i
    j (i = i1) → r j

■-refl₁ : {A : Type ℓ} {x y : A} (p : x ≡ y) → refl ■ p ≡ p
■-refl₁ p i j = ■-square refl p (i ∨ j) j

■-refl₂ : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ■ refl ≡ p
■-refl₂ p i j =  ■-square p refl (~ i ∧ j) j

■-inv : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ■ inv p ≡ refl
■-inv {x = x} p i j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → ■-square p (inv p) (j ∧ k) j
    k (i = i1) → p (j ∧ ~ k)
    k (j = i0) → x
    k (j = i1) → p (~ k)
    k (k = i0) → p j

ap-■ : {A : Type ℓ₁} {B : Type ℓ₂} {x y z : A} (f : A → B) (p : x ≡ y) (q : y ≡ z) → ap f (p ■ q) ≡ ap f p ■ ap f q
ap-■ {y = y} f p q i j =
  i ► ap-hcomp (∂ j) f λ where
    k (j = i0) → p (~ k)
    k (j = i1) → q k
    k (k = i0) → y

square-triangle₁ : {A : Type ℓ} {ul ur ll lr : A} {p : ul ≡ ur} {q : ul ≡ ll} {r : ur ≡ lr} {s : ll ≡ lr}
  (α : Square p q r s) → diag α ≡ p ■ r
square-triangle₁ {ur = ur} {p = p} {r = r} α i j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → α (j ∨ ~ k) (j ∧ k)
    k (i = i1) → ■-square p r (j ∨ ~ k) (j ∧ k)
    k (j = i0) → p (~ k)
    k (j = i1) → r k
    k (k = i0) → ur

square-triangle₂ : {A : Type ℓ} {ul ur ll lr : A} {p : ul ≡ ur} {q : ul ≡ ll} {r : ur ≡ lr} {s : ll ≡ lr}
  (α : Square p q r s) → diag α ≡ q ■ s
square-triangle₂ {ll = ll} {q = q} {s = s} α i j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → α (j ∧ k) (j ∨ ~ k)
    k (i = i1) → ■-square q s (j ∧ k) (j ∨ ~ k)
    k (j = i0) → q (~ k)
    k (j = i1) → s k
    k (k = i0) → ll

■-assoc-square : {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → Square (p ■ q) p r (q ■ r)
■-assoc-square p q r i j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) (j = i0) → p (~ k)
    k (i = i1) (j = i0) → q k
    k (j = i0) → ■-square p q (i ∧ k) (i ∨ ~ k)
    k (i = i0) → p (j ∨ ~ k)
    k (i = i1) → ■-square q r j k
    k (j = i1) → ■-square q r i (i ∧ k)
    k (k = i0) → q (i ∧ j)

■-assoc : {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → (p ■ q) ■ r ≡ p ■ (q ■ r)
■-assoc p q r =
  let α = ■-assoc-square p q r
  in inv (square-triangle₁ α) ■ square-triangle₂ α

{-
■-cube : {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  Cube λ where
    i j k (i = i0) → ■-square p q j k
    i j k (i = i1) → ■-square q r j k
    i j k (j = i0) → ■-square p q i k
    i j k (j = i1) → ■-square q r i k
    i j k (k = i0) → ■-square p q i j
    i j k (k = i1) → ■-square q r i j
■-cube p q r i j k =
  hcomp ((∂ i ∧ ∂ j) ∨ (∂ j ∧ ∂ k) ∨ (∂ i ∧ ∂ k)) λ where
    h (i = i0) (j = i0) → p (k ∨ ~ h)
    h (i = i0) (j = i1) → q (k ∧ h)
    h (i = i1) (j = i0) → q (k ∨ ~ h)
    h (i = i1) (j = i1) → r (k ∧ h)
    h (j = i0) (k = i0) → {!p (i ∨ ~ h)!}
    h (j = i0) (k = i1) → {!!}
    h (j = i1) (k = i0) → {!!}
    h (j = i1) (k = i1) → {!!}
    h (i = i0) (k = i0) → {!!}
    h (i = i1) (k = i0) → {!!}
    h (i = i0) (k = i1) → {!!}
    h (i = i1) (k = i1) → {!!}
    h (h = i0) → {!!}
-}

infix 6 _■⟨QED⟩
_■⟨QED⟩ : ∀ {A : Type ℓ} (x : A) → x ≡ x
_ ■⟨QED⟩ = refl

infixr 5 _■⟨_⟩_
_■⟨_⟩_ : {A : Type ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ■⟨ p ⟩ q = p ■ q

infixr 5 _■⟨=⟩_
_■⟨=⟩_ : {A : Type ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
_ ■⟨=⟩ p = p

Ω₁ : {A : Type ℓ} → A → Type ℓ
Ω₁ x = x ≡ x

Ω : ℕ → {A : Type ℓ} → A → Type ℓ
Ω-base : (n : ℕ) → {A : Type ℓ} (x : A) → Ω n x

Ω zero {A} _ = A
Ω (succ n) x = Ω₁ (Ω-base n x)
Ω-base zero x = x
Ω-base (succ n) x = refl-at (Ω-base n x)

Ω₂ : {A : Type ℓ} → A → Type ℓ
Ω₂ = Ω 2

Ω₃ : {A : Type ℓ} → A → Type ℓ
Ω₃ = Ω 3

eckmann-hilton : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : Ω₂ x)
  → ┌ q ┐
    p · p
    └ q ┘
eckmann-hilton {x = x} p q i j k =
  hcomp (∂ i ∨ ∂ j ∨ ∂ k) λ where
    t (i = i0) → p j (t ∧ k)
    t (i = i1) → p j (t ∧ k)
    t (j = i0) → q i (~ t ∨ k)
    t (j = i1) → q i (~ t ∨ k)
    t (k = i0) → q i (~ t)
    t (k = i1) → p j t
    t (t = i0) → x

infixr 30 _■ᶜ_
_■ᶜ_ : ∀ {ℓ} {A : Type ℓ} {x : A} (α β : Ω₂ x) → Ω₂ x
(α ■ᶜ β) i = eckmann-hilton α β i i

repeat : {A : Type ℓ} {x : A} → ℕ → Ω₁ x → Ω₁ x
repeat 0 _ = refl
repeat 1 p = p
repeat (succ (succ n)) p = p ■₃ repeat n p ■₃ p

repeatₗ : {A : Type ℓ} {x : A} → ℕ → Ω₁ x → Ω₁ x
repeatₗ 0 _ = refl
repeatₗ 1 p = p
repeatₗ (succ (succ n)) p = p ■₃ p ■₃ repeatₗ n p

repeatᵣ : {A : Type ℓ} {x : A} → ℕ → Ω₁ x → Ω₁ x
repeatᵣ 0 _ = refl
repeatᵣ 1 p = p
repeatᵣ (succ (succ n)) p = repeatᵣ n p ■₃ p ■₃ p


shadow : {A : Type ℓ} → A → A
shadow x = hcomp i0 λ where
  t (t = i0) → x

shadow-id : {A : Type ℓ} → shadow ≡ id
shadow-id {A = A} i x =
  the A $ hcomp (i ≈ i1) λ where
    j (i = i1) → x
    j (j = i0) → x

hcomp-empty : {A : Type ℓ} (floor : A) → shadow floor ≡ floor
hcomp-empty floor i = hcomp (i ≈ i1) λ where
  j (i = i1) → floor
  j (j = i0) → floor

transpot-id : {A : Type ℓ} → transpot ≡ id
transpot-id {A = A} i = transp (λ _ → A) (i ≈ i1)

transport-■ : {A B C : Type ℓ} (p : A ≡ B) (q : B ≡ C)
  → transport (p ■ q) ≡ transport q ∘ transport p
transport-■ p q i = transport q ∘ transpot-id i ∘ transport p

transport-inv : {A B : Type ℓ} (p : A ≡ B)
  → transport (inv p) ∘ transport p ≡ id
transport-inv p i =
  hcomp (∂ i) λ where
    j (i = i0) → transport-■ p (inv p) j
    j (j = i0) → transport (■-inv p i)
    j (i = i1) → transpot-id j

pathₚ : (A : I → Type ℓ) {x : A i0} {y : A i1} → transport (λ i → A i) x ≡ y → Path A x y
pathₚ A {x = x} p i =
  hcomp (∂ i) λ where
    j (i = i0) → x
    j (j = i0) → transp (λ t → A (i ∧ t)) (i ≈ i0) x
    j (i = i1) → p j

⊥-hcomp : {A : Type ℓ} → ⊥ → (φ : I) (f : Partial φ A) → Sub A φ f
⊥-hcomp ()

BasedPath : {A : Type ℓ} → A → Type ℓ
BasedPath x = Σ _ λ y → x ≡ y

contract : {A : Type ℓ} (x : A) (α : BasedPath x) → (x , refl) ≡ α
fst (contract x (y , p) i) = p i
snd (contract x (y , p) i) j = p (i ∧ j)
