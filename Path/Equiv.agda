{-# OPTIONS --cubical --erasure --allow-unsolved-metas #-}
module Path.Equiv where

open import Prelude
open import Path.Comp
open import Data.Truncation.Base

opaque
  lrinv′ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
    (𝓪 𝓫 : IsEquiv f) → linv 𝓪 ≡ rinv 𝓫
  lrinv′ {f = f} 𝓪 𝓫 =
    linv 𝓪 ■⟨ (λ i b → linv 𝓪 (is-rinv 𝓫 (~ i) b)) ⟩
    linv 𝓪 ∘ f ∘ rinv 𝓫 ■⟨ (λ i b → is-linv 𝓪 i (rinv 𝓫 b)) ⟩
    rinv 𝓫 ■⟨QED⟩

  lrinv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
    (𝓪 : IsEquiv f) → linv 𝓪 ≡ rinv 𝓪
  lrinv 𝓪 = lrinv′ 𝓪 𝓪

  llinv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
    (α β : IsEquiv f) → linv α ≡ linv β
  llinv α β = lrinv′ α β ■ inv (lrinv β)

  rrinv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
    (α β : IsEquiv f) → rinv α ≡ rinv β
  rrinv α β = inv (lrinv α) ■ lrinv′ α β

  is-llinv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
    (α β : IsEquiv f) → Path (λ i → llinv α β i ∘ f ≡ id) (is-linv α) (is-linv β)
  is-llinv α β i j x = {! !}

equiv-prop : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} → IsProp (IsEquiv f)
linv (equiv-prop α β i) = llinv α β i
rinv (equiv-prop α β i) = rrinv α β i
is-linv (equiv-prop α β i) j x = {! !}
is-rinv (equiv-prop α β i) = {! !}

linv-is-rinv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
  (α : IsEquiv f) → f ∘ linv α ≡ id
linv-is-rinv {f = f} α = transport (λ t → f ∘ lrinv α (~ t) ≡ id) (is-rinv α)

{-
linv (equiv-prop 𝓪 𝓫 i) = (lrinv′ 𝓪 𝓫 ■ inv (lrinv 𝓫)) i
-- g =ᵣ g f h′ =ₗ h′ =ₗ g′ f h′ =ᵣ g′
-- g f =ᵣ g f h′ f =ₗ h′ f =ₗ g′ f h′ f =ᵣ g′ f =ₗ id
rinv (equiv-prop 𝓪 𝓫 i) = (inv (lrinv 𝓪) ■ lrinv′ 𝓪 𝓫) i
is-linv (equiv-prop 𝓪 𝓫 i) a = {!equiv-prop 𝓪 𝓫!}
is-rinv (equiv-prop 𝓪 𝓫 i) = {!!}
-}

equiv-inj : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (α : A ≅ B) {x y : A} → fun α x ≡ fun α y → x ≡ y
equiv-inj α p =
  (λ i → is-linv (is-equiv α) (~ i) _) ■₃
  (λ i → linv (is-equiv α) (p i)) ■₃
  (λ i → is-linv (is-equiv α) i _)

equiv-equal : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (α β : A ≅ B) → fun α ≡ fun β → α ≡ β
fun (equiv-equal α β p i) = p i
is-equiv (equiv-equal α β p i) = dprop (λ i → IsEquiv (p i)) equiv-prop (is-equiv α) (is-equiv β) i

id-equiv : ∀ {ℓ} (A : Type ℓ) → IsEquiv (id {A = A})
linv (id-equiv A) = id
rinv (id-equiv A) = id
is-linv (id-equiv A) = refl
is-rinv (id-equiv A) = refl

∘-equiv : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {f : B → C} {g : A → B}
  → IsEquiv f → IsEquiv g → IsEquiv (f ∘ g)
linv (∘-equiv 𝓯 𝓰) = linv 𝓰 ∘ linv 𝓯
rinv (∘-equiv 𝓯 𝓰) = rinv 𝓰 ∘ rinv 𝓯
is-linv (∘-equiv {g = g} 𝓯 𝓰) = (λ i → linv 𝓰 ∘ is-linv 𝓯 i ∘ g) ■ is-linv 𝓰
is-rinv (∘-equiv {f = f} 𝓯 𝓰) = (λ i → f ∘ is-rinv 𝓰 i ∘ rinv 𝓯) ■ is-rinv 𝓯

linv-equiv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
  (𝓯 : IsEquiv f) → IsEquiv (linv 𝓯)
linv (linv-equiv {f = f} _) = f
rinv (linv-equiv {f = f} _) = f
is-linv (linv-equiv {f = f} 𝓯) = (λ i → f ∘ lrinv 𝓯 i) ■ is-rinv 𝓯
is-rinv (linv-equiv 𝓯) = is-linv 𝓯

transport-equiv : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → IsEquiv (transport p)
linv (transport-equiv p) = transport (inv p)
rinv (transport-equiv p) = transport (inv p)
is-linv (transport-equiv p) i a =
  hcomp (∂ i) λ where
    j (i = i0) → transport-■ p (inv p) j a
    j (j = i0) → transport (■-inv p i) a
    j (i = i1) → transpot-id j a
is-rinv (transport-equiv p) i b =
  hcomp (∂ i) λ where
    j (i = i0) → transport-■ (inv p) p j b
    j (j = i0) → transport (■-inv (inv p) i) b
    j (i = i1) → transpot-id j b

≅-id : ∀ {ℓ} {A : Type ℓ} → A ≅ A
fun ≅-id = id
is-equiv ≅-id = id-equiv _

_≅-∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → A ≅ B → B ≅ C → A ≅ C
fun (α ≅-∘ β) = fun β ∘ fun α
is-equiv (α ≅-∘ β) = ∘-equiv (is-equiv β) (is-equiv α)

≅-inv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
  → A ≅ B → B ≅ A
fun (≅-inv α) = linv (is-equiv α)
is-equiv (≅-inv α) = linv-equiv (is-equiv α)

path-equiv : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A ≅ B
fun (path-equiv p) = transport p
is-equiv (path-equiv p) = transport-equiv p

glue-path : ∀ {ℓ} {A B C : Type ℓ} → A ≅ B → C ≅ B → A ≡ C
glue-path {A = A} {B = B} {C = C} α β i =
  Glue B
    (λ { (i = i0) → A ; (i = i1) → C })
    (λ { (i = i0) → α ; (i = i1) → β })

equiv-path : ∀ {ℓ} {A B : Type ℓ} → A ≅ B → A ≡ B
equiv-path {A = A} {B = B} α = glue-path α ≅-id

-- equiv-path₁ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B C : A → Type ℓ₂} → (∀ x → B x ≅ C x) → 

from-equiv-path : ∀ {ℓ} {A B : Type ℓ} (α : A ≅ B) (i : I) → equiv-path α i → B
from-equiv-path α i x = unglue {e = λ { (i = i0) → α ; (i = i1) → ≅-id }} x

transport-equiv-path : ∀ {ℓ} {A B : Type ℓ} (α : A ≅ B) (x : A) → Path′ (equiv-path α) x (fun α x)
transport-equiv-path α x i =
  glue
    (λ where
      (i = i0) → x
      (i = i1) → fun α x)
    (fun α x)

transport-path : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : A) → Path′ p x (transport p x)
transport-path p x = todo where postulate todo : Path′ p x (transport p x)
  -- glue (λ { (i = i0) → x ; (i = i1) → fun α x }) (fun α x)

{-
type-equiv-equiv : ∀ {ℓ} {A B : Type ℓ} (α β : A ≅ B) → (α ≡ β) ≅ (fun α ≡ fun β)
fun (type-equiv-equiv α β) = ap fun
fun (linv (is-equiv (type-equiv-equiv α β)) p i) = p i
is-equiv (linv (is-equiv (type-equiv-equiv α β)) p i) =
  prop-fill (λ _ → equiv-prop) (λ { i (i = i0) → is-equiv α ; i (i = i1) → is-equiv β }) i
fun (rinv (is-equiv (type-equiv-equiv α β)) p i) = p i
is-equiv (rinv (is-equiv (type-equiv-equiv α β)) p i) =
  prop-fill (λ _ → equiv-prop) (λ { i (i = i0) → is-equiv α ; i (i = i1) → is-equiv β }) i
fun (is-linv (is-equiv (type-equiv-equiv α β)) j p i) = fun (p i)
is-equiv (is-linv (is-equiv (type-equiv-equiv α β)) j p i) =
  set-fill (λ _ _ → prop-to-set equiv-prop) ? i j
is-rinv (is-equiv (type-equiv-equiv α β)) = {! !}

type-path-equiv : ∀ {ℓ} {A B : Type ℓ} (p q : A ≡ B) → (p ≡ q) ≅ (transport p ≡ transport q)
fun (type-path-equiv p q) α i = transport (α i)
linv (is-equiv (type-path-equiv p q)) = {! !}
rinv (is-equiv (type-path-equiv p q)) = {! !}
is-linv (is-equiv (type-path-equiv p q)) = {! !}
is-rinv (is-equiv (type-path-equiv p q)) = {! !}
-}

path-equiv-refl : ∀ {ℓ} (A : Type ℓ) → path-equiv (refl-at A) ≡ ≅-id
fun (path-equiv-refl A i) = transpot-id i
is-equiv (path-equiv-refl A i) = dprop (λ i → IsEquiv (transpot-id i)) equiv-prop (transport-equiv (refl-at A)) (id-equiv A) i

path-equiv-■ : ∀ {ℓ} {A B C : Type ℓ} (p : A ≡ B) (q : B ≡ C) → path-equiv (p ■ q) ≡ path-equiv p ≅-∘ path-equiv q
fun (path-equiv-■ p q i) = transport-■ p q i
is-equiv (path-equiv-■ p q i) = dprop (λ i → IsEquiv (transport-■ p q i)) equiv-prop (transport-equiv (p ■ q)) (∘-equiv (transport-equiv q) (transport-equiv p)) i

path-equiv-inv : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → path-equiv (inv p) ≡ ≅-inv (path-equiv p)
fun (path-equiv-inv p i) = transport (inv p)
is-equiv (path-equiv-inv p i) = equiv-prop (transport-equiv (inv p)) (linv-equiv (transport-equiv p)) i

inv-is-equiv : ∀ {ℓ} {A : Type ℓ} {x y : A} → IsEquiv (inv {x = x} {y = y})
linv inv-is-equiv = inv
rinv inv-is-equiv = inv
is-linv inv-is-equiv = refl
is-rinv inv-is-equiv = refl

inv-equiv : ∀ {ℓ} {A : Type ℓ} {x y : A} → (x ≡ y) ≅ (y ≡ x)
fun inv-equiv = inv
is-equiv inv-equiv = inv-is-equiv

inv-path : ∀ {ℓ} {A : Type ℓ} {x y : A} → (x ≡ y) ≡ (y ≡ x)
inv-path = equiv-path inv-equiv

flip-equiv : ∀ {ℓ₁ ℓ₂ ℓ₃} (A : Type ℓ₁) (B : Type ℓ₂) (C : Type ℓ₃) → (A → B → C) ≅ (B → A → C)
fun (flip-equiv A B C) = flip
linv (is-equiv (flip-equiv A B C)) = flip
rinv (is-equiv (flip-equiv A B C)) = flip
is-linv (is-equiv (flip-equiv A B C)) = refl
is-rinv (is-equiv (flip-equiv A B C)) = refl

flip-path : ∀ {ℓ₁ ℓ₂ ℓ₃} (A : Type ℓ₁) (B : Type ℓ₂) (C : Type ℓ₃) → (A → B → C) ≡ (B → A → C)
flip-path A B C = equiv-path (flip-equiv A B C)

⊥-equiv : ∀ {ℓ} {A : Type ℓ} → ¬ A → A ≅ ⊥
fun (⊥-equiv f) = f
linv (is-equiv (⊥-equiv f)) ()
rinv (is-equiv (⊥-equiv f)) ()
is-linv (is-equiv (⊥-equiv f)) i x = the (linv (is-equiv (⊥-equiv f)) (fun (⊥-equiv f) x) ≡ x) (absurd $ f x) i
is-rinv (is-equiv (⊥-equiv f)) _ ()

⊥-path : {A : Type} → ¬ A → A ≡ ⊥
⊥-path f = equiv-path (⊥-equiv f)
