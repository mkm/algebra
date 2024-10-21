{-# OPTIONS --rewriting --confluence-check #-}
module OTT where

open import Agda.Primitive

data ⊥ : Set where

record ⊤ : Set where
  eta-equality
  constructor *

record Σ {ℓ} (A : Set ℓ) (B : A → Set ℓ) : Set ℓ where
  eta-equality
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

infix 2 Σ

_×_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
A × B = Σ[ _ ∶ A ] B

postulate
  _↦_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
  _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
  id : ∀ {ℓ} {A : Set ℓ} (x : A) → x ≡ x
  transport : ∀ {ℓ ℓ′} {A : Set ℓ} (B : A → Set ℓ′) {x y : A} → x ≡ y → B x → B y
  ⊤-eq : (* ≡ *) ↦ ⊤
  ×-eq : ∀ {ℓ} {A B : Set ℓ} {a a′ : A} {b b′ : B} → (a , b) ≡ (a′ , b′) ↦ (a ≡ a′) × (b ≡ b′)
  Σ-eq : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {a a′ : A} {b : B a} {b′ : B a′} → (a , b) ≡ (a′ , b′) ↦ Σ[ p ∶ a ≡ a′ ] transport B p b ≡ b′
  transport-const : ∀ {ℓ} {A : Set ℓ} (B : Set ℓ) {x y : A} {b : B} (p : x ≡ y) → transport (λ _ → B) p b ↦ b
  ×-transport : ∀ {ℓ} {A : Set ℓ} {B₁ B₂ : A → Set ℓ} {a a′ : A} {p : a ≡ a′} {b₁ : B₁ a} {b₂ : B₂ a} → transport (λ a → B₁ a × B₂ a) p (b₁ , b₂) ↦ (transport B₁ p b₁ , transport B₂ p b₂)
  ×-transport-const : ∀ {ℓ} {A : Set ℓ} {B₁ B₂ : Set ℓ} {a a′ : A} {p : a ≡ a′} {b₁ : B₁} {b₂ : B₂} → transport (λ a → B₁ × B₂) p (b₁ , b₂) ↦ (b₁ , b₂)
  Σ-transport : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {C : (a : A) → B a → Set ℓ} {a a′ : A} {p : a ≡ a′} {b : B a} {c : C a b} → transport (λ a → Σ (B a) (C a)) p (b , c) ↦ (transport B p b , {!!})

infix 1 _↦_
infix 3 _≡_

{-# BUILTIN REWRITE _↦_ #-}
{-# REWRITE ⊤-eq Σ-eq transport-const ×-transport ×-transport-const #-}

postulate
  ×-id : ∀ {ℓ} {A B : Set ℓ} {a : A} {b : B} → id (a , b) ↦ (id a , id b)

{-# REWRITE ×-id #-}

record ⟨_⟩ {ℓ} (A : Set ℓ) : Set ℓ where
  field
    elem : A
    unique : ∀ a → elem ≡ a

open ⟨_⟩

record _≈_ {ℓ} (A B : Set ℓ) : Set (lsuc ℓ) where
  field
    corr : A → B → Set ℓ
    fwd : ∀ a → ⟨ Σ[ b ∶ B ] corr a b ⟩
    bwd : ∀ b → ⟨ Σ[ a ∶ A ] corr a b ⟩

open _≈_ public

map-fwd : ∀ {ℓ} {A B : Set ℓ} → A ≈ B → A → B
map-fwd φ a = fst (elem (fwd φ a))

postulate
  Set-eq : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ↦ (A ≈ B)

{-# REWRITE Set-eq #-}

postulate
  Set-transport : ∀ {ℓ} {A B : Set ℓ} {p : A ≡ B} → transport (λ X → X) p ↦ map-fwd p

{-# REWRITE Set-transport #-}

⊤-is-prop : (x y : ⊤) → x ≡ y
⊤-is-prop _ _ = *

×-comm : ∀ {ℓ} (A B : Set ℓ) → A × B ≡ B × A
corr (×-comm A B) (a , b) (b′ , a′) = (a ≡ a′) × (b ≡ b′)
elem (fwd (×-comm A B) (a , b)) = (b , a) , (id a , id b)
unique (fwd (×-comm A B) (a , b)) ((b′ , a′) , (p , q)) = (q , p) , ({!!} , {!!})
bwd (×-comm A B) = {!!}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_ℕ-≡_ : ℕ → ℕ → Set
zero ℕ-≡ zero = ⊤
zero ℕ-≡ succ n = ⊥
succ m ℕ-≡ zero = ⊥
succ m ℕ-≡ succ n = m ℕ-≡ n

postulate
  ℕ-eq : {m n : ℕ} → (m ≡ n) ↦ (m ℕ-≡ n)

{-# REWRITE ℕ-eq #-}
