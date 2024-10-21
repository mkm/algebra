{-# OPTIONS --cubical --erasure #-}
module Data.Sigma where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Data.Truncation

Σ-prop : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} → IsProp A → (∀ x → IsProp (B x)) → IsProp (Σ A B)
fst (Σ-prop A-prop B-prop x y i) = A-prop (fst x) (fst y) i
snd (Σ-prop A-prop B-prop x y i) =
  prop-fill (λ i → B-prop (A-prop (fst x) (fst y) i)) i
    λ where
      i (i = i0) → snd x
      i (i = i1) → snd y

Σ-set : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} → IsSet A → (∀ x → IsSet (B x)) → IsSet (Σ A B)
fst (Σ-set A-set B-set x y p q i j) = A-set (fst x) (fst y) (ap fst p) (ap fst q) i j
snd (Σ-set A-set B-set x y p q i j) =
  set-fill (λ i j → B-set (A-set (fst x) (fst y) (ap fst p) (ap fst q) i j)) i j
    λ where
      i j (j = i0) → snd x
      i j (i = i0) → snd (p j)
      i j (i = i1) → snd (q j)
      i j (j = i1) → snd y

×-prop : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → IsProp A → IsProp B → IsProp (A × B)
×-prop A-prop B-prop = Σ-prop A-prop (λ _ → B-prop)

×-set : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → IsSet A → IsSet B → IsSet (A × B)
×-set A-set B-set = Σ-set A-set (λ _ → B-set)

module _ {ℓ ℓ′ ℓ″} (A : Type ℓ) (B : A → Type ℓ′) (C : (x : A) → B x → Type ℓ″) where

  Σ-assoc-fun : (Σ (Σ A B) λ (x , y) → C x y) → (Σ A λ x → Σ (B x) λ y → C x y)
  Σ-assoc-fun ((x , y) , z) = x , (y , z)

  Σ-assoc-inv : (Σ A λ x → Σ (B x) λ y → C x y) → (Σ (Σ A B) λ (x , y) → C x y)
  Σ-assoc-inv (x , (y , z)) = (x , y) , z

  Σ-assoc-equiv : (Σ (Σ A B) λ (x , y) → C x y) ≅ (Σ A λ x → Σ (B x) λ y → C x y)
  fun Σ-assoc-equiv = Σ-assoc-fun
  linv (is-equiv Σ-assoc-equiv) = Σ-assoc-inv
  rinv (is-equiv Σ-assoc-equiv) = Σ-assoc-inv
  is-linv (is-equiv Σ-assoc-equiv) = refl
  is-rinv (is-equiv Σ-assoc-equiv) = refl

  Σ-assoc : (Σ (Σ A B) λ (x , y) → C x y) ≡ (Σ A λ x → Σ (B x) λ y → C x y)
  Σ-assoc = equiv-path Σ-assoc-equiv

×-assoc : ∀ {ℓ ℓ′ ℓ″} (A : Type ℓ) (B : Type ℓ′) (C : Type ℓ″)
  → (A × B) × C ≡ A × (B × C)
×-assoc A B C = Σ-assoc A (λ _ → B) (λ _ _ → C)

Σ-path : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} {x y : Σ A B}
  → (p : fst x ≡ fst y) → Path (λ i → B (p i)) (snd x) (snd y) → x ≡ y
Σ-path p q i = p i , q i

Σ-path-equiv : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} (x y : Σ A B)
  → (x ≡ y) ≅ Σ (fst x ≡ fst y) λ p → Path (λ i → B (p i)) (snd x) (snd y)
fun (Σ-path-equiv x y) p = (λ i → fst (p i)) , (λ i → snd (p i))
linv (is-equiv (Σ-path-equiv x y)) (p , q) i = p i , q i
rinv (is-equiv (Σ-path-equiv x y)) (p , q) i = p i , q i
is-linv (is-equiv (Σ-path-equiv x y)) _ = id
is-rinv (is-equiv (Σ-path-equiv x y)) _ = id

Σ-path-char : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} (x y : Σ A B)
  → (x ≡ y) ≡ Σ (fst x ≡ fst y) λ p → Path (λ i → B (p i)) (snd x) (snd y)
Σ-path-char x y = equiv-path (Σ-path-equiv x y)

{-
prop-type-set : ∀ ℓ → IsSet (PropType ℓ)
prop-type-set ℓ A B =
  transport (λ t → IsProp (Σ-path-char A B (~ t))) λ (p , q) (p′ , q′) i → {! !} , {! !}
-}
