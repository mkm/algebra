{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Symmetry where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Control.Monad
open import Data.Truncation
open import Data.Truncation.Equiv
open import Data.Bool
open import Data.Nat hiding (max)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level

infixr 0 _→ₛ_
record _→ₛ_ (A : Type ℓ₁) (B : Type ℓ₂) : Type (lsuc ℓ₁ ⊔ ℓ₂) where
  field
    Ix : Type ℓ₁
    eqv : A ≅₀ Ix
    map : Ix → B

open _→ₛ_

sym : {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → A →ₛ B
Ix (sym {A = A} f) = A
eqv (sym f) = ≅₀-id
map (sym f) = f

idₛ : {A : Type ℓ} → A →ₛ A
Ix (idₛ {A = A}) = A
eqv idₛ = ≅₀-id
map idₛ = id

_∘ₛ_ : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} → (B → C) → (A →ₛ B) → A →ₛ C
Ix (f ∘ₛ g) = Ix g
eqv (f ∘ₛ g) = eqv g
map (f ∘ₛ g) = f ∘ map g

permute : {A B : Type ℓ₁} {C : Type ℓ₂} → (B →ₛ C) → A ≅₀ B → A →ₛ C
Ix (permute f α) = Ix f
eqv (permute f α) = α ≅₀-∘ eqv f
map (permute f α) = map f

{-
record Πₛ (A : Type ℓ₁) (B : A →ₛ Type ℓ₂) : Type (lsuc ℓ₁ ⊔ ℓ₂) where
  field
    IxD : Type ℓ₁
    eqvd : ∣ A ≡ IxD ∣₀
    mapd : (x : IxD) → {!permute B (map-∣∣₀ inv eqvd)!}
-}

infixr 20 _,ₛ_
_,ₛ_ : {A : Type ℓ} → A → A → Bool →ₛ A
x ,ₛ y = sym $ bool-rec x y

rec-sym-prop : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} → IsProp C
  → ((A → B) → C) → (A →ₛ B) → C
rec-sym-prop C-prop f s = recall₀ C-prop do
  e ← eqv s
  pure $ f (map s ∘ fun e)

private
  module RecSet {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
      (C-set : IsSet C) (f : (A → B) → C)
      (p : {J : Type ℓ₁} (m : J → B) (α β : A ≅ J) → f (m ∘ fun α) ≡ f (m ∘ fun β))
      (J : Type ℓ₁) (m : J → B) where

    rec-sym-set : A ≅₀ J → C
    rec-sym-set-collapse : (α β : A ≅₀ J) → rec-sym-set α ≡ rec-sym-set β
    rec-sym-set-forget : A ≅ J → C
    rec-sym-set-forget-forget : (α β : A ≅ J) → rec-sym-set-forget α ≡ rec-sym-set-forget β
    rec-sym-set-collapse-forget : (α : A ≅ J) (β : A ≅₀ J) → rec-sym-set-forget α ≡ rec-sym-set β

    rec-sym-set (forget₀ α) = rec-sym-set-forget α
    rec-sym-set (collapse₀ α β i) = rec-sym-set-collapse α β i

    rec-sym-set-collapse (forget₀ α) β = rec-sym-set-collapse-forget α β
    rec-sym-set-collapse (collapse₀ α β i) γ j =
      set-fill (λ _ _ → C-set) i j λ where
        i j (j = i0) → rec-sym-set-collapse α β i
        i j (i = i0) → rec-sym-set-collapse α γ j
        i j (i = i1) → rec-sym-set-collapse β γ j
        i j (j = i1) → rec-sym-set γ

    rec-sym-set-forget α = f (m ∘ fun α)

    rec-sym-set-forget-forget α β = p m α β

    rec-sym-set-collapse-forget α (forget₀ β) = rec-sym-set-forget-forget α β
    rec-sym-set-collapse-forget α (collapse₀ β γ i) j =
      set-fill (λ _ _ → C-set) i j λ where
        i j (j = i0) → f (m ∘ fun α)
        i j (i = i0) → rec-sym-set-collapse-forget α β j
        i j (i = i1) → rec-sym-set-collapse-forget α γ j
        i j (j = i1) → rec-sym-set-collapse β γ i

rec-sym-set : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → IsSet C → (f : (A → B) → C) → ({J : Type ℓ₁} (m : J → B) (α β : A ≅ J) → f (m ∘ fun α) ≡ f (m ∘ fun β)) → (A →ₛ B) → C
rec-sym-set C-set f p s = RecSet.rec-sym-set C-set f p (Ix s) (map s) (eqv s)

private
  module RecGroupoid {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
    (C-groupoid : IsGroupoid C) (f : (A → B) → C)
    (p : {J : Type ℓ₁} (m : J → B) (α β : A ≅ J) → f (m ∘ fun α) ≡ f (m ∘ fun β))
    (q : {J : Type ℓ₁} (m : J → B) (α β γ : A ≅ J) → Path (λ i → p m α β i ≡ f (m ∘ fun γ)) (p m α γ) (p m β γ))
    (J : Type ℓ₁) (m : J → B) where

    rec : A ≅₀ J
      → C
    rec-forget : A ≅ J
      → C
    rec-collapse : (α β : A ≅₀ J)
      → rec α ≡ rec β
    rec-collapse-forget : (α : A ≅ J) (β : A ≅₀ J)
      → rec-forget α ≡ rec β
    rec-collapse-forget-forget : (α β : A ≅ J)
      → rec-forget α ≡ rec-forget β
    rec-collapse-collapse : (α β γ : A ≅₀ J)
      → Path (λ i → rec-collapse α β i ≡ rec γ) (rec-collapse α γ) (rec-collapse β γ)
    rec-collapse-collapse-forget : (α : A ≅ J) (β γ : A ≅₀ J)
      → Path (λ i → rec-collapse-forget α β i ≡ rec γ) (rec-collapse-forget α γ) (rec-collapse β γ)
    rec-collapse-collapse-forget-forget : (α β : A ≅ J) (γ : A ≅₀ J)
      → Path (λ i → rec-collapse-forget-forget α β i ≡ rec γ) (rec-collapse-forget α γ) (rec-collapse-forget β γ)
    rec-collapse-collapse-forget-forget-forget : (α β γ : A ≅ J)
      → Path (λ i → rec-collapse-forget-forget α β i ≡ rec-forget γ) (rec-collapse-forget-forget α γ) (rec-collapse-forget-forget β γ)

    rec (forget₀ α) = rec-forget α
    rec (collapse₀ α β i) = rec-collapse α β i

    rec-forget α = f (m ∘ fun α)

    rec-collapse (forget₀ α) β = rec-collapse-forget α β
    rec-collapse (collapse₀ α β i) γ = rec-collapse-collapse α β γ i

    rec-collapse-forget α (forget₀ β) = rec-collapse-forget-forget α β
    rec-collapse-forget α (collapse₀ β γ i) = {! !}

    rec-collapse-forget-forget α β = p m α β

    rec-collapse-collapse (forget₀ α) β γ = {! !}
    rec-collapse-collapse (collapse₀ α β i) γ δ j k = {! !}

    rec-collapse-collapse-forget α (forget₀ β) γ = {! !}
    rec-collapse-collapse-forget α (collapse₀ β γ i) δ = {! !}

    rec-collapse-collapse-forget-forget α β (forget₀ γ) = rec-collapse-collapse-forget-forget-forget α β γ
    rec-collapse-collapse-forget-forget α β (collapse₀ γ δ i) j k = {! !}

    rec-collapse-collapse-forget-forget-forget α β γ i j = q m α β γ i j

rec-upair : {A : Type ℓ₁} {B : Type ℓ₂} → IsSet B → (m : A → A → B) → (∀ x y → m x y ≡ m y x) → (Bool →ₛ A) → B
rec-upair B-set m p = rec-sym-set B-set (λ f → m (f false) (f true)) λ g α β → {! !}

{-
rec-upair ℬ m p = rec-sym-set ℬ (λ f → m (f false) (f true)) λ f → ind-bool-aut (λ α → m (f false) (f true) ≡ m (f (transport α false)) (f (transport α true))) refl (p _ _)

maxₛ : (Bool →ₛ ℕ) → ℕ
maxₛ = rec-upair ℕ-set max max-comm
  where
    max : ℕ → ℕ → ℕ
    max zero zero = zero
    max zero (succ b) = succ b
    max (succ a) zero = succ a
    max (succ a) (succ b) = succ (max a b)
    max-comm : ∀ a b → max a b ≡ max b a
    max-comm zero zero = refl
    max-comm zero (succ b) = refl
    max-comm (succ a) zero = refl
    max-comm (succ a) (succ b) i = succ (max-comm a b i)

glue-elem : {A B : Type ℓ} (α : A ≅ B) (x : A) → Path′ (equiv-path α) x (fun α x)
glue-elem α x i = glue (λ { (i = i0) → x ; (i = i1) → fun α x }) (fun α x)
-}

_,ₛₛ_ : {A : Type ℓ} (x y : A) → x ,ₛ y ≡ y ,ₛ x
Ix ((x ,ₛₛ y) i) = not-path i
eqv ((x ,ₛₛ y) i) = {! !} -- dprop (λ i → ∣ Bool ≡ not-path i ∣₀) collapse₀ (forget₀ refl) (forget₀ refl) i
map (_,ₛₛ_ {A = A} x y i) =
  hcomp (∂ i) λ where
    j (i = i0) → bool-rec x y
    j (j = i0) → transp (λ t → not-path (i ∧ t) → A) (i ≈ i0) (bool-rec x y)
    j (i = i1) → lemma j
  where
    lemma : transpot ∘ bool-rec x y ∘ transport (λ j → not-path (~ j)) ≡ bool-rec y x
    lemma j false = transpot-id j y
    lemma j true = transpot-id j x

_,ₛₛₛ_ : {A : Type ℓ} (x y : A) → Path′ inv-path (x ,ₛₛ y) (y ,ₛₛ x)
x ,ₛₛₛ y = {!!}

Pathₛ′ : {A : Type ℓ} {B : Type} → ∣ Bool ≡ B ∣₀ → (B → A) → Type ℓ
Pathₛ′ (forget₀ α) f = f (transport α false) ≡ f (transport α true)
Pathₛ′ (collapse₀ α₁ α₂ i) f = {!!}

Pathₛ : {A : Type ℓ} → (Bool →ₛ A) → Type ℓ
Pathₛ s with eqv s
Pathₛ s | forget₀ α = map s (fun α false) ≡ map s (fun α true)
Pathₛ s | collapse₀ (forget₀ α) (forget₀ β) i = {! !}
Pathₛ s | collapse₀ (forget₀ α) (collapse₀ (forget₀ β) (forget₀ γ) i) j = {! !}
Pathₛ s | collapse₀ (forget₀ α) (collapse₀ β γ i) j = {! !}
Pathₛ s | collapse₀ α β i = {! !}
