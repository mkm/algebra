{-# OPTIONS --cubical --erasure #-}
module Path.Char where

open import Prelude
open import Path.Comp

fn-path : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
fn-path p i x = p x i

{-
fn-pathₚ : ∀ {ℓ₁ ℓ₂} {A : I → Type ℓ₁} {B : I → Type ℓ₂} {f : A i0 → B i0} {g : A i1 → B i1} → (∀ x → transp B i0 (f x) ≡ g (transp A i0 x)) → Path (λ i → A i → B i) f g
fn-pathₚ p i x = {!!}
-}

Σ-path : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} {(x , y) (x′ , y′) : Σ A B} (p : x ≡ x′) → Path (λ i → B (p i)) y y′ → (x , y) ≡ (x′ , y′)
Σ-path p q i = p i , q i

Σ-path² : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
  {(ul , ul′) (ur , ur′) (ll , ll′) (lr , lr′) : Σ A B}
  {p : ul ≡ ur} {p′ : Path (λ i → B (p i)) ul′ ur′} {q : ul ≡ ll} {q′ : Path (λ i → B (q i)) ul′ ll′} {r : ur ≡ lr} {r′ : Path (λ i → B (r i)) ur′ lr′} {s : ll ≡ lr} {s′ : Path (λ i → B (s i)) ll′ lr′}
  → (α : Square p q r s) → SquareP (λ i j → B (α i j)) p′ q′ r′ s′
  → Square {A = Σ A B} (Σ-path p p′) (Σ-path q q′) (Σ-path r r′) (Σ-path s s′) 
Σ-path² α β i j = α i j , β i j

≡-path : ∀ {ℓ} {A : Type ℓ} {x y : A} {p q : x ≡ y} → Path (λ i → p i ≡ q i) refl refl → p ≡ q
≡-path p i j = p j i
