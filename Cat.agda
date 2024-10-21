{-# OPTIONS --cubical --prop #-}
module Cat where

open import Path using (Type)
open import Nat

data Term : Type where
  𝒰 : ℕ → Term
  op : Term
  ↑ : Term
  ↓ : Term
  hom : Term
  iso : Term
  * : Term
  ⊥ : Term
  prod : Term
  sum : Term
  fix : Term
  id : Term
  _∘_ : Term → Term → Term
  _∘′_ : Term → Term → Term
  unit : Term
  app : Term
  lam : Term → Term
  absurd : Term
  fst : Term
  snd : Term
  _,_ : Term → Term → Term
  inl : Term
  inr : Term
  case : Term → Term → Term
  fold : Term
  unfold : Term
  rec : Term → Term

infixr 100 _∘_ _∘′_

prop : Term
prop = 𝒰 1

ord : Term
ord = 𝒰 2

ocat : Term
ocat = 𝒰 3

Δ : Term
Δ = id , id

_⊕_ : Term → Term → Term
a ⊕ b = (a , b) ∘ sum

infixr 21 _⊕_

_×_ : Term → Term → Term
a × b = (a , b) ∘ prod

infixr 22 _×_

_⇒_ : Term → Term → Term
a ⇒ b = (a , b) ∘ hom

infixr 20 _⇒_

_⇔_ : Term → Term → Term
a ⇔ b = (a , b) ∘ iso

⌜_⌝ : Term → Term
⌜ f ⌝ = lam (snd ∘ f)

infix 110 ⌜_⌝

const : Term → Term
const f = unit ∘ f

‵ℕ : Term
‵ℕ = ⌜ unit ∘ * × id ⌝ ∘ fix

‵zero : Term
‵zero = (id ∘′ inl) ∘ fold

data ⊢_∶_⟶_ : Term → Term → Term → Type

data ⊢_≈_ : Term → Term → Type

data ⊢_∶_⟶_ where
  t-𝒰 : ∀ {δ} →
    ⊢ 𝒰 δ ∶ * ⟶ 𝒰 (succ δ)
  t-op : ∀ {a} →
    ⊢ op ∶ a ⟶ a ∘ op
  t-↑ : ∀ {δ} →
    ⊢ ↑ ∶ 𝒰 δ ⟶ 𝒰 (succ δ) ∘ ↓
  t-↓ : ∀ {δ} →
    ⊢ ↓ ∶ 𝒰 (succ δ) ⟶ 𝒰 δ ∘ ↑
  t-hom : ∀ {a} →
    (δ : ℕ) →
    ⊢ hom ∶ a ∘ op × a ⟶ 𝒰 (pred δ)
  t-iso : ∀ {δ a} →
    ⊢ iso ∶ a ∘ op × a ⟶ 𝒰 (pred δ)
  t-* : ∀ {δ} →
    ⊢ * ∶ * ⟶ 𝒰 δ
  t-⊥ : ∀ {δ} →
    ⊢ ⊥ ∶ * ⟶ 𝒰 (1 + δ)
  t-prod : ∀ {δ} →
    ⊢ prod ∶ 𝒰 δ × 𝒰 δ ⟶ 𝒰 δ
  t-sum : ∀ {δ} →
    ⊢ sum ∶ 𝒰 δ × 𝒰 δ ⟶ 𝒰 (max 2 δ)
  t-fix : ∀ {δ} →
    ⊢ fix ∶ 𝒰 δ ⇒ 𝒰 δ ⟶ 𝒰 δ
  t-id : ∀ {a} →
    ⊢ id ∶ a ⟶ a
  t-∘ : ∀ {a b c f g} →
    ⊢ f ∶ a ⟶ b →
    ⊢ g ∶ b ⟶ c →
    ⊢ f ∘ g ∶ a ⟶ c
  t-∘′ : ∀ {a b c f g h k α β} →
    ⊢ f ∶ a ⟶ b →
    ⊢ g ∶ a ⟶ b →
    ⊢ h ∶ b ⟶ c →
    ⊢ k ∶ b ⟶ c →
    ⊢ α ∶ f ⟶ g →
    ⊢ β ∶ h ⟶ k →
    ⊢ α ∘′ β ∶ f ∘ h ⟶ g ∘ k
  t-unit : ∀ {a} →
    ⊢ unit ∶ a ⟶ *
  t-app : ∀ {a b} →
    ⊢ app ∶ (a ⇒ b) × a ⟶ b
  t-lam : ∀ {a b c f} →
    ⊢ f ∶ a × b ⟶ c →
    ⊢ lam f ∶ a ⟶ b ⇒ c
  t-absurd : ∀ {a} →
    ⊢ absurd ∶ ⊥ ⟶ a
  t-fst : ∀ {a b} →
    ⊢ fst ∶ a × b ⟶ a
  t-snd : ∀ {a b} →
    ⊢ snd ∶ a × b ⟶ b
  t-pair : ∀ {a b c f g} →
    ⊢ f ∶ a ⟶ b →
    ⊢ g ∶ a ⟶ c →
    ⊢ (f , g) ∶ a ⟶ b × c
  t-inl : ∀ {a b} →
    ⊢ inl ∶ a ⟶ a ⊕ b
  t-inr : ∀ {a b} →
    ⊢ inr ∶ b ⟶ a ⊕ b
  t-case : ∀ {a b c f g} →
    ⊢ f ∶ a ⟶ c →
    ⊢ g ∶ b ⟶ c →
    ⊢ case f g ∶ a ⊕ b ⟶ c
  t-fold : ∀ {δ τ} →
    ⊢ τ ∶ 𝒰 δ ⟶ 𝒰 δ →
    ⊢ fold ∶ ⌜ τ ⌝ ∘ fix ∘ τ ⟶ ⌜ τ ⌝ ∘ fix
  t-unfold : ∀ {δ τ} →
    ⊢ τ ∶ 𝒰 δ ⟶ 𝒰 δ →
    ⊢ unfold ∶ ⌜ τ ⌝ ∘ fix ⟶ ⌜ τ ⌝ ∘ fix ∘ τ
    {-
  t-rec : ∀ {τ} →
    ⊢ τ ∶ 𝒰 δ ⟶ 𝒰 δ →
    ⊢ f ∶ 
    ⊢ rec f ∶ ⌜ τ ⌝ ∘ fix ⟶ a
  -}

data ⊢_≈_ where
  e-refl : ∀ {a} →
    ⊢ a ≈ a
  e-sym : ∀ {a b} →
    ⊢ a ≈ b →
    ⊢ b ≈ a
  e-trans : ∀ {a b c} →
    ⊢ a ≈ b →
    ⊢ b ≈ c →
    ⊢ a ≈ c
  e-↑-↓ :
    ⊢ ↑ ∘ ↓ ≈ id

infix 2 ⊢_∶_⟶_ ⊢_≈_

-- subtyping? universe sequences?

t-prop : ⊢ prop ∶ * ⟶ ord
t-prop = t-𝒰

t-Δ : ∀ {a} → ⊢ Δ ∶ a ⟶ (a , a) ∘ prod
t-Δ = t-pair t-id t-id

t-⇒ : ∀ {a b f g} (δ : ℕ) → ⊢ f ∶ a ⟶ b ∘ op → ⊢ g ∶ a ⟶ b → ⊢ f ⇒ g ∶ a ⟶ 𝒰 (pred δ)
t-⇒ δ 𝒯₁ 𝒯₂ = t-∘ (t-pair 𝒯₁ 𝒯₂) (t-hom δ)

t-⌜_⌝ : ∀ {a b f} → ⊢ f ∶ a ⟶ b → ⊢ ⌜ f ⌝ ∶ * ⟶ a ⇒ b
t-⌜ 𝒯 ⌝ = t-lam (t-∘ t-snd 𝒯)

t-const : ∀ {a b f} → ⊢ f ∶ * ⟶ b → ⊢ const f ∶ a ⟶ b
t-const 𝒯 = t-∘ t-unit 𝒯

t-‵ℕ : ⊢ ‵ℕ ∶ * ⟶ 𝒰 2
t-‵ℕ = t-∘ t-⌜ t-∘ (t-pair (t-∘ t-unit t-*) t-id) t-prod ⌝ t-fix

t-‵zero : ⊢ ‵zero ∶ unit ⟶ ‵ℕ
t-‵zero = {!!}

record Sanity (a b a′ b′ : Term) : Type where
  field
    san₁ : ⊢ a ≈ a′
    san₂ : ⊢ b ≈ b′

sanity : ∀ {a b a′ b′ f g} → ⊢ f ∶ a ⟶ b → ⊢ g ∶ a′ ⟶ b′ → ⊢ f ≈ g → Sanity a b a′ b′
sanity 𝒯₁ 𝒯₂ e-refl = {!!}
sanity 𝒯₁ 𝒯₂ (e-sym ℰ) = {!!}
sanity 𝒯₁ 𝒯₂ (e-trans ℰ₁ ℰ₂) = {!!}
sanity 𝒯₁ 𝒯₂ e-↑-↓ = {!!}

module Hurkens where
  not : Term
  not = (id ⇒ const ⊥) ∘ ↑

  t-not : ⊢ not ∶ ord ∘ op ⟶ ord ∘ ↓
  t-not = t-∘ (t-⇒ 2 t-id (t-∘ t-unit t-⊥)) t-↑

  {-
    P a° = ↑° a° ⇒ ord
    ↑° ∶ 𝒰 δ ∘ op ⟶ 𝒰 δ₊ ∘ op
    *   [𝒰 δ]    𝒰 δ₊     [op] 𝒰 δ₊ ∘ op
         ⟦↑⟧                ⟦ψ⟧
    * [𝒰 δ₊ ∘ ↓] 𝒰 δ₊ ∘ ↑ [op] 𝒰 δ₊₊ ∘ op
   -}

  P : Term
  P = (↑ ∘′ id ⇒ const ord)

  t-P : ⊢ P ∶ ord ∘ op ⟶ ord ∘ ↓
  t-P = {!!} -- t-⇒ 3 (t-∘′ {!t-𝒰!} t-𝒰 t-op t-op t-↑ t-id) (t-const t-𝒰)
