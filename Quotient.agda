{-# OPTIONS --cubical --prop #-}
module Quotient where

open import Path
open import Logic
open import Nat
-- open import Suspension
open import Cube

module _ (A : Type) (_∼_ : A → A → Type) where
  data _/_ : Type

  A/∼ : Type
  A/∼ = _/_

  QRim : ℕ → Type

  QPath : ∀ {n} → QRim n → QRim n → Type

  data QCube : ℕ → Type

  qrim : ∀ {n} → QCube n → QRim n

  data QCube where
    qc-const : ∀ {n} (a : A) → QCube n
    qc-quot : ∀ {a b} → a ∼ b → QCube 1
    qc-fill : ∀ {n} → QRim n → QCube n

  record QCyl (n : ℕ) : Type where
    inductive
    field
      q-floor : QCube n
      q-ceil : QCube n
      q-wall : QPath (qrim q-floor) (qrim q-ceil)

  open QCyl

  QRim zero = ♯ ⊥
  QRim (succ n) = QCyl n

  QPath {succ _} qr₁ qr₂ = {!QPath (q-floor qr₁) (q-floor qr₂)!}

  -- how to define synthetic higher-dimensional paths?

  qrim qc = {!!}

  to-rim : ∀ {n} → QRim n → Rim n → A/∼
  
  to-cube : ∀ {n} → QCube n → Cube n → A/∼

  data _/_ where
    ⟨_⟩ : A → A/∼
    quot : ∀ {a b} → a ∼ b → ⟨ a ⟩ ≡ ⟨ b ⟩
    triv-fill : ∀ {n} (p : QRim n) → Cube n → A/∼
    triv-rim : ∀ {n} (p : QRim n) (◻ : Rim n) → triv-fill p (rim ◻) ≡ to-rim p ◻
--    triv-fill : ∀ {n} {p : Rim n → A/∼} → TrivRim p → Cube n → A/∼
--    triv-rim : ∀ {n} {p : Rim n → A/∼} (τ : TrivRim p) (◻ : Rim n) → triv-fill τ (rim ◻) ≡ p ◻

  to-rim qr = {!!}

  to-cube (qc-const a) = λ _ → ⟨ a ⟩
  to-cube (qc-quot e) = cube₁ λ i → quot e i
  to-cube (qc-fill qr) = triv-fill qr

  test : ∀ {a b : A} (e₁ : a ∼ b) (e₂ : b ∼ a) → quot e₁ =⟦ i ⊢ ⟨ a ⟩ ≡ quot e₂ i ⟧= id
  test {a = a} e₁ e₂ = {!triv-fill !}
    where
      r : Rim 2 → A/∼
      r = rim₂ λ { i j (i = i0) → quot e₁ j
                 ; i j (i = i1) → ⟨ a ⟩
                 ; i j (j = i0) → ⟨ a ⟩
                 ; i j (j = i1) → quot e₂ i }

{-
module _ (A : Type) (_∼_ : A → A → Type) (∼-id : ∀ a → a ∼ a) (_∼-∘_ : ∀ {a b c} → a ∼ b → b ∼ c → a ∼ c) where
  data _∼′_ : A → A → Type where
    [] : ∀ {a} → a ∼′ a
    _∷_ : ∀ {a b c} → a ∼ b → b ∼′ c → a ∼′ c

  data Quot : Type

  A/∼ : Type
  A/∼ = Quot

  data Quot where
    ⟨_⟩ : A → A/∼
    collapse : ∀ {a b} → ! (a ∼ b) → ⟨ a ⟩ ≡ ⟨ b ⟩
    -- collapse : ∀ {a b} → a ≢ b → ! (a ∼ b) → ⟨ a ⟩ ≡ ⟨ b ⟩
    collapse-id : ∀ a → collapse ∣ ∼-id a ∣ ≡ id
    collapse-∘ : ∀ {a b c} (p : a ∼ b) (q : b ∼ c) → collapse ∣ p ∼-∘ q ∣ ≡ collapse ∣ p ∣ ∘ collapse ∣ q ∣

    -- proving inequality precondition should be possible polymorphic containers

module Test where
  open import Circle

  data Seg : Type where
    s0 : Seg
    s1 : Seg
    seg : s0 ≡ s1

  data _∼_ : Seg → Seg → Type where
    tunnel : s0 ∼ s1

  ∼-id : (s : Seg) → s ∼ s
  ∼-id s0 = transport (t ⊢ s0 ∼ seg (~ t)) tunnel
  ∼-id s1 = transport (t ⊢ seg t ∼ s1) tunnel
  ∼-id (seg i) = transport (t ⊢ seg (i ∧ t) ∼ seg (~ t ∨ i)) tunnel

  _∼-∘_ : ∀ {s₁ s₂ s₃} → s₁ ∼ s₂ → s₂ ∼ s₃ → s₁ ∼ s₃
  _∼-∘_ {s₃ = s₃} tunnel q = transport (t ⊢ seg (~ t) ∼ s₃) q

  Seg/∼ : Type
  Seg/∼ = Quot Seg _∼_ ∼-id _∼-∘_

  to-S¹ : Seg/∼ → S¹
  to-S¹ ⟨ s0 ⟩ = base
  to-S¹ ⟨ s1 ⟩ = base
  to-S¹ ⟨ seg i ⟩ = loop i
  to-S¹ (collapse {a = s0} {b = s0} p k) = base
  to-S¹ (collapse {a = s0} {b = s1} p k) = base
  to-S¹ (collapse {a = s0} {b = seg j} p k) = {!collapse p!}
  to-S¹ (collapse {a = s1} {b = s₂} p k) = {!!}
  to-S¹ (collapse {a = seg i} {b = s₂} p k) = {!!}
  to-S¹ (collapse-id s i j) = {!!}
  to-S¹ (collapse-∘ p q i j) = {!!}
-}

{-
module _ (A : Type) (_∼_ : A → A → Type) where
  data _/_ : Type

  A/∼ : Type
  A/∼ = _/_

  ⟨_⟩′ : A → A/∼

  is-link : {n : ℕ} → (Cube n → A/∼) → Prop
  is-link = {!!}

  essence : {n : ℕ} {a : A} → L n ⟨ a ⟩′ → L n a

  core : {n : ℕ} → (S n → A/∼) → (S n → A)

  data _/_ where
    ⟨_⟩ : A → A/∼
    quotient : {a b : A} → a ∼ b → ⟨ a ⟩ ≡ ⟨ b ⟩
    trunc : (n : ℕ) {a : A} (ℓ : L n ⟨ a ⟩′) (σ : S n) → ℓ .path σ ≡ ⟨ essence ℓ .path σ ⟩
--    trunc : (n : ℕ) (p : S n → A/∼) → p ≡ (λ σ → ⟨ core p σ ⟩)

  ⟨_⟩′ = ⟨_⟩

  essence = {!!}

  core₁ : (p q : Cube 1 → A/∼) → {!!}
  core₁ p q = {!!}

  core′ : {n : ℕ} → (p : Cube n → A/∼) → Type
  core′ = {!!}

  core p σ = {!!}

  is-link₁′ : {a : A} (x : A/∼) → ⟨ a ⟩ ≡ x → x ≡ ⟨ a ⟩ → Type
  is-link₁′ ⟨ b ⟩ p q = ! (p ≡ inv q)
  is-link₁′ (quotient _ _) p q = ! (p ≡ inv q)
  is-link₁′ (trunc n ℓ σ i) p q = {!!}

  is-link₁ : {a : A} → ⟨ a ⟩ ≡ ⟨ a ⟩ → I → Type
  is-link₁ {a} p i = is-link₁′ (p i) (λ j → p (i ∧ j)) (λ j → p (i ∨ j))

  -- encode-decode, characterise paths?
  -- use _/_ for quotienting paths codes?
-}

{-
data _/_ A _∼_ where
  ⟨_⟩ : A → A / _∼_
  quotient : {x y : A} → x ∼ y → ⟨ x ⟩ ≡ ⟨ y ⟩
  trunc : (n : ℕ) (p : S n → A / _∼_) → ((q : S n → A) → ¬ (∀ σ → p σ ≡ ⟨ q σ ⟩)) → p ≡ (λ _ → p base)
-}

{-
data Lim (T : ℕ → Type) (E : ∀ {n} → T n → T (succ n)) : Type where
  ⟨_⟩ : {n : ℕ} → T n → Lim T E
  embed : {n : ℕ} (x : T n) → ⟨ E x ⟩ ≡ ⟨ x ⟩

data _/′_ (A : Type) (P : A → A → Type) : Type where
  ⟨_⟩ : A → A /′ P
  equiv : ∀ {x y} → P x y → ⟨ x ⟩ ≡ ⟨ y ⟩

Q : ℕ → (A : Type) (P : A → A → Type) → Type
Q zero A P = A /′ P
Q (succ n) A P = Q n A P /′ {!!}
-}
