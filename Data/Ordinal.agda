{-# OPTIONS --cubical --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Data.Ordinal where

open import Prelude renaming (zero to zero′; succ to succ′)
open import Path.Comp
open import Path.Equiv
open import Data.Truncation

data Ord : Type

_≤_ : Ord → Ord → Type
_<_ : Ord → Ord → Type

data Ord where
  zero : Ord
  succ : Ord → Ord
  lim : (ℕ → Ord) → Ord
  equinum : ∀ α β → α ≤ β → β ≤ α → α ≡ β
  ord-set : IsSet Ord

ord-ind-prop : ∀ {ℓ} {A : Ord → Type ℓ} → (∀ α → IsProp (A α))
  → A zero → (∀ {α} → A α → A (succ α)) → (∀ {αs} → (∀ n → A (αs n)) → A (lim αs)) → (α : Ord) → A α
ord-ind-prop A-prop z s l zero = z
ord-ind-prop A-prop z s l (succ α) = s (ord-ind-prop A-prop z s l α)
ord-ind-prop A-prop z s l (lim αs) = l (λ n → ord-ind-prop A-prop z s l (αs n))
ord-ind-prop A-prop z s l (equinum α β le₁ le₂ i) =
  prop-fill (λ i → A-prop (equinum α β le₁ le₂ i)) i
    λ where
      i (i = i0) → ord-ind-prop A-prop z s l α
      i (i = i1) → ord-ind-prop A-prop z s l β
ord-ind-prop A-prop z s l (ord-set α β p q i j) =
  set-fill (λ i j → prop-to-set (A-prop (ord-set α β p q i j))) i j
    λ where
      i j (j = i0) → ord-ind-prop A-prop z s l α
      i j (i = i0) → ord-ind-prop A-prop z s l (p j)
      i j (i = i1) → ord-ind-prop A-prop z s l (q j)
      i j (j = i1) → ord-ind-prop A-prop z s l β

{-# TERMINATING #-}
_≤′_ : Ord → Ord → PropType₀
{-# TERMINATING #-}
_<′_ : Ord → Ord → PropType₀

α ≤ β = fst (α ≤′ β)
α < β = fst (α <′ β)

≤-prop : ∀ α β → IsProp (α ≤ β)
≤-prop α β = snd (α ≤′ β)

<-prop : ∀ α β → IsProp (α < β)
<-prop α β = snd (α <′ β)

≤≤ : ∀ α β γ → α ≤ β → β ≤ γ → α ≤ γ
<≤ : ∀ α β γ → α < β → β ≤ γ → α < γ
≤< : ∀ α β γ → α ≤ β → β < γ → α < γ

<≤-lim : ∀ α βs γ → α < lim βs → lim βs ≤ γ → α < γ
≤<-lim : ∀ α β γs → α ≤ β → β < lim γs → α < lim γs

≤-cong₁ : ∀ α α′ β → α ≤ α′ → α′ ≤ α → (α ≤ β) ≅ (α′ ≤ β)
fun (≤-cong₁ α α′ β le₁ le₂) = ≤≤ α′ α β le₂
linv (is-equiv (≤-cong₁ α α′ β le₁ le₂)) = ≤≤ α α′ β le₁
rinv (is-equiv (≤-cong₁ α α′ β le₁ le₂)) = ≤≤ α α′ β le₁
is-linv (is-equiv (≤-cong₁ α α′ β le₁ le₂)) i le′ = ≤-prop α β (≤≤ α α′ β le₁ (≤≤ α′ α β le₂ le′)) le′ i
is-rinv (is-equiv (≤-cong₁ α α′ β le₁ le₂)) i le′ = ≤-prop α′ β (≤≤ α′ α β le₂ (≤≤ α α′ β le₁ le′)) le′ i

<-cong₁ : ∀ α α′ β → α ≤ α′ → α′ ≤ α → (α < β) ≅ (α′ < β)
fun (<-cong₁ α α′ β le₁ le₂) = ≤< α′ α β le₂
linv (is-equiv (<-cong₁ α α′ β le₁ le₂)) = ≤< α α′ β le₁
rinv (is-equiv (<-cong₁ α α′ β le₁ le₂)) = ≤< α α′ β le₁
is-linv (is-equiv (<-cong₁ α α′ β le₁ le₂)) i le′ = <-prop α β (≤< α α′ β le₁ (≤< α′ α β le₂ le′)) le′ i
is-rinv (is-equiv (<-cong₁ α α′ β le₁ le₂)) i le′ = <-prop α′ β (≤< α′ α β le₂ (≤< α α′ β le₁ le′)) le′ i

<-cong₂ : ∀ α β β′ → β ≤ β′ → β′ ≤ β → (α < β) ≅ (α < β′)
fun (<-cong₂ α β β′ le₁ le₂) le′ = <≤ α β β′ le′ le₁
linv (is-equiv (<-cong₂ α β β′ le₁ le₂)) le′ = <≤ α β′ β le′ le₂
rinv (is-equiv (<-cong₂ α β β′ le₁ le₂)) le′ = <≤ α β′ β le′ le₂
is-linv (is-equiv (<-cong₂ α β β′ le₁ le₂)) i le′ = <-prop α β (<≤ α β′ β (<≤ α β β′ le′ le₁) le₂) le′ i
is-rinv (is-equiv (<-cong₂ α β β′ le₁ le₂)) i le′ = <-prop α β′ (<≤ α β β′ (<≤ α β′ β le′ le₂) le₁) le′ i

zero ≤′ β = ⊤ , ⊤-prop
succ α ≤′ β = α <′ β
lim αs ≤′ β = (∀ n → αs n ≤ β) , pi-prop λ n → ≤-prop (αs n) β
equinum α α′ le₁ le₂ i ≤′ β =
  equiv-path (≤-cong₁ α α′ β le₁ le₂) i , prop-fill (λ _ → is-prop-prop) i sys
  where
    sys : (i : I) → Partial (∂ i) (IsProp (equiv-path (≤-cong₁ α α′ β le₁ le₂) i))
    sys i (i = i0) = ≤-prop α β
    sys i (i = i1) = ≤-prop α′ β
ord-set α α′ p q i j ≤′ β = prop-type-set (α ≤′ β) (α′ ≤′ β) (λ j → p j ≤′ β) (λ j → q j ≤′ β) i j

α <′ zero = ⊥ , ⊥-prop
α <′ succ β = α ≤′ β
α <′ lim βs = ∣ Σ ℕ (λ n → (α < βs n)) ∣₀ , collapse₀
α <′ equinum β β′ le₁ le₂ i =
  equiv-path (<-cong₂ α β β′ le₁ le₂) i , prop-fill (λ _ → is-prop-prop) i sys
  where
    sys : (i : I) → Partial (∂ i) (IsProp (equiv-path (<-cong₂ α β β′ le₁ le₂) i))
    sys i (i = i0) = <-prop α β
    sys i (i = i1) = <-prop α β′
α <′ ord-set β β′ p q i j = prop-type-set (α <′ β) (α <′ β′) (λ j → α <′ p j) (λ j → α <′ q j) i j

≤≤ zero β γ le₁ le₂ = tt
≤≤ (succ α) β γ le₁ le₂ = <≤ α β γ le₁ le₂
≤≤ (lim αs) β γ le₁ le₂ n = ≤≤ (αs n) β γ (le₁ n) le₂
≤≤ (equinum α α′ le₁′ le₂′ i) β γ le₁ le₂ =
  hcomp (∂ i) λ where
    j (i = i0) → ≤-prop α γ base (≤≤ α β γ le₁ le₂) j
    j (j = i0) → base
    j (i = i1) → ≤-prop α′ γ base (≤≤ α′ β γ le₁ le₂) j
  where
    base : equiv-path (≤-cong₁ α α′ γ le₁′ le₂′) i
    base = transport-equiv-path (≤-cong₁ α α′ γ le₁′ le₂′) (≤≤ α β γ (≤≤ α α′ β le₁′ (from-equiv-path (≤-cong₁ α α′ β le₁′ le₂′) i le₁)) le₂) i
≤≤ (ord-set α α′ p q i j) β γ le₁ le₂ =
  hcomp (∂ i ∨ ∂ j) λ where
    k (j = i0) → ≤≤ α β γ le₁ le₂ -- f i i0 is-one
    k (i = i0) → {! ≤≤ (p j) β γ le₁ le₂ !} -- f i0 j is-one
    k (i = i1) → {! ≤≤ (q j) β γ le₁ le₂ !} -- f i1 j is-one
    k (j = i1) → ≤≤ α′ β γ le₁ le₂ -- dset (λ i → A-set i i1) (f i0 i1 is-one) (f i1 i1 is-one) (λ i → base i i1) (λ i → f i i1 is-one) k i
    k (k = i0) → base i
  where
    base : (i : I) → ord-set α α′ p q i j ≤ γ
    base =
      fill (λ i → ord-set α α′ p q i j ≤ γ) (∂ j)
        λ where
          i (j = i0) → ≤≤ α β γ le₁ le₂
          i (i = i0) → hcomp (∂ j) λ where -- prop-fill (λ j → ≤-prop (p j) γ) j
            k (j = i0) → ?
            k (k = i0) → {! ≤≤ (p j) β γ le₁ le₂ !}
            k (j = i1) → ?
          i (j = i1) → ≤≤ α′ β γ le₁ le₂
{-
  set-fill {A = λ i₁ j₁ → ord-set α α′ p q i₁ j₁ ≤ γ} {! !} i j
    λ where
      i j (j = i0) → {! ≤≤ α β γ le₁ le₂ !}
      i j (i = i0) → {! ≤≤ (p j) β γ le₁ le₂ !}
      i j (i = i1) → {! ≤≤ (q j) β γ le₁ le₂ !}
      i j (j = i1) → {! ≤≤ α′ β γ le₁ le₂ !}
-}

<≤ α (succ β) γ le₁ le₂ = ≤< α β γ le₁ le₂
<≤ α (lim βs) γ le₁ le₂ = <≤-lim α βs γ le₁ le₂
<≤ α (equinum β β′ le₁′ le₂′ i) γ le₁ le₂ =
  hcomp (∂ i) λ where
    j (i = i0) → <-prop α γ base (<≤ α β γ le₁ le₂) j
    j (j = i0) → base
    j (i = i1) → <-prop α γ base (<≤ α β′ γ le₁ le₂) j
  where
    base : α < γ
    base = <≤ α β′ γ (from-equiv-path (<-cong₂ α β β′ le₁′ le₂′) i le₁) (from-equiv-path (≤-cong₁ β β′ γ le₁′ le₂′) i le₂)
<≤ α (ord-set β β′ p q i j) γ le₁ le₂ = {! !}

≤< α β (succ γ) le₁ le₂ = ≤≤ α β γ le₁ le₂
≤< α β (lim γs) le₁ le₂ = ≤<-lim α β γs le₁ le₂
≤< α β (equinum γ γ′ le₁′ le₂′ i) le₁ le₂ =
  hcomp (∂ i) λ where
    j (i = i0) → <-prop α γ base (≤< α β γ le₁ le₂) j
    j (j = i0) → base
    j (i = i1) → <-prop α γ′ base (≤< α β γ′ le₁ le₂) j
  where
    base : equiv-path (<-cong₂ α γ γ′ le₁′ le₂′) i
    base = transport-equiv-path (<-cong₂ α γ γ′ le₁′ le₂′) (≤< α β γ le₁ (<≤ β γ′ γ (from-equiv-path (<-cong₂ β γ γ′ le₁′ le₂′) i le₂) le₂′)) i
≤< α β (ord-set γ γ′ p q i j) le₁ le₂ = {! !}

<≤-lim α βs γ (forget₀ (n , le₁)) le₂ = <≤ α (βs n) γ le₁ (le₂ n)
<≤-lim α βs γ (collapse₀ le₁ le₁′ i) le₂ = <-prop α γ (<≤-lim α βs γ le₁ le₂) (<≤-lim α βs γ le₁′ le₂) i

≤<-lim α β γs le₁ (forget₀ (n , le₂)) = forget₀ (n , ≤< α β (γs n) le₁ le₂)
≤<-lim α β γs le₁ (collapse₀ le₂ le₂′ i) = collapse₀ (≤<-lim α β γs le₁ le₂) (≤<-lim α β γs le₁ le₂′) i

{-
≤-prop : ∀ α β → IsProp (α ≤ β)
<-prop : ∀ α β → IsProp (α < β)
≤≤ : ∀ α β γ → α ≤ β → β ≤ γ → α ≤ γ
<≤ : ∀ α β γ → α < β → β ≤ γ → α < γ
≤< : ∀ α β γ → α ≤ β → β < γ → α < γ

zero ≤ β = ⊤
succ α ≤ β = α < β
lim α⁻ ≤ β = ∀ n → α⁻ n ≤ β
equinum α α′ x y i ≤ β = prop-path (≤-prop α β) (≤-prop α′ β) (≤≤ α′ α β y) (≤≤ α α′ β x) i
ord-set α α′ p q i j ≤ β =
  hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → prop-path (≤-prop (q j) β) (≤-prop (p j) β) (transp (λ t → p (j ∧ t) ≤ β) (j ≈ i0) ∘ transp (λ t → q (j ∧ ~ t) ≤ β) (j ≈ i0)) (transp (λ t → q (j ∧ t) ≤ β) (j ≈ i0) ∘ transp (λ t → p (j ∧ ~ t) ≤ β) (j ≈ i0)) k
    k (i = i1) → prop-path (≤-prop (q j) β) (≤-prop (q j) β) id id k
    k (j = i0) → prop-path (≤-prop α β) (≤-prop α β) id id k
    -- k (j = i1) (i = i0) → prop-path (≤-prop α′ β) (≤-prop α′ β) (transport (λ t → p t ≤ β) ∘ transport (λ t → q (~ t) ≤ β)) (transport (λ t → q t ≤ β) ∘ transport (λ t → p (~ t) ≤ β)) k
    k (j = i1) → prop-path-prop (≤-prop α′ β) (≤-prop α′ β)
      (prop-path (≤-prop α′ β) (≤-prop α′ β) (transport (λ t → p t ≤ β) ∘ transport (λ t → q (~ t) ≤ β)) (transport (λ t → q t ≤ β) ∘ transport (λ t → p (~ t) ≤ β)))
      (prop-path (≤-prop α′ β) (≤-prop α′ β) id id) i k 
    -- k (j = i1) (i = i1) → prop-path (≤-prop α′ β) (≤-prop α′ β) id id k
    k (k = i0) → q j ≤ β

α < zero = ⊥
α < succ β = α ≤ β
α < lim β⁻ = Σ ℕ λ n → α < β⁻ n
α < equinum β β′ x y i = prop-path (<-prop α β) (<-prop α β′) (λ z → <≤ α β β′ z x ) (λ z → <≤ α β′ β z y) i
α < ord-set β β′ x y i j = {!!}

≤-prop zero β x y = refl
≤-prop (succ α) β x y = <-prop α β x y
≤-prop (lim α⁻) β x y i n = ≤-prop (α⁻ n) β (x n) (y n) i
≤-prop (equinum α α′ z w i) β x y j = {! dprop (λ i → equinum α α′ z w i ≤ β) (≤-prop α β)   !}
≤-prop (ord-set α α′ p q i j) β x y = {!!}

<-prop α (succ β) x y = ≤-prop α β x y
<-prop α (lim β⁻) x y = {!!}
<-prop α (equinum β β′ z w i) x y = {!!}
<-prop α (ord-set β β′ z w i j) x y = {!!}

≤≤ zero β γ x y = tt
≤≤ (succ α) β γ x y = <≤ α β γ x y
≤≤ (lim α⁻) β γ x y n = ≤≤ (α⁻ n) β γ (x n) y
≤≤ (equinum α α′ z w i) β γ x y = {!!}
≤≤ (ord-set α α′ z w i j) β γ x y = {!!}

<≤ α (succ β) γ x y = ≤< α β γ x y
<≤ α (lim β⁻) γ (n , x) y = <≤ α (β⁻ n) γ x (y n)
-- <≤ α (lim β⁻) γ (forget₀ (n , x)) y = <≤ α (β⁻ n) γ x (y n)
-- <≤ α (lim β⁻) γ (collapse₀ x x′ i) y = {!!} -- <-prop α γ (<≤ α (lim β⁻) γ x y) (<≤ α (lim β⁻) γ x′ y) i
<≤ α (equinum β β′ z w i) γ x y = {!!}
<≤ α (ord-set β β′ z w i j) γ x y = {!!}

≤< α β (succ γ) x y = ≤≤ α β γ x y
≤< α β (lim γ⁻) x (n , y) = n , ≤< α β (γ⁻ n) x y
-- ≤< α β (lim γ⁻) x (collapse₀ y y′ i) = <-prop α (lim γ⁻) (≤< α β (lim γ⁻) x y) (≤< α β (lim γ⁻) x y′) i
≤< α β (equinum γ γ′ z w i) x y = {!!}
≤< α β (ord-set γ γ′ z w i j) x y = {!!}

ord-to-prop : ∀ {ℓ} {A : Ord → Type ℓ} → (∀ α → IsProp (A α)) → A zero → (∀ {α} → A α → A (succ α)) → (∀ α⁻ → (∀ n → A (α⁻ n)) → A (lim α⁻)) → (α : Ord) → A α
ord-to-prop 𝒜 z s l zero = z
ord-to-prop 𝒜 z s l (succ α) = s $ ord-to-prop 𝒜 z s l α
ord-to-prop 𝒜 z s l (lim α⁻) = l _ λ n → ord-to-prop 𝒜 z s l (α⁻ n)
ord-to-prop {A = A} 𝒜 z s l (equinum α α′ x y i) =
  prop-fill (𝒜 (equinum α α′ x y i)) i0 i witness λ where
    (i = i0) → ord-to-prop 𝒜 z s l α
    (i = i1) → ord-to-prop 𝒜 z s l α′
  where
    witness : _
    witness = transport (λ t → A (equinum α α′ x y (i ∧ t))) (ord-to-prop 𝒜 z s l α)
ord-to-prop {A = A} 𝒜 z s l (ord-set α α′ x y i j) =
  prop-fill (𝒜 (ord-set α α′ x y i j)) (∂ i) j witness λ where
    (i = i0) → ord-to-prop 𝒜 z s l (x j)
    (i = i1) → ord-to-prop 𝒜 z s l (y j)
    (j = i0) → ord-to-prop 𝒜 z s l α
    (j = i1) → ord-to-prop 𝒜 z s l α′
  where
    witness : _
    witness = transport (λ t → A (ord-set α α′ x y (i ∧ t) (j ∧ t))) (ord-to-prop 𝒜 z s l α)

≤-lim′ : ∀ α β⁻ n → α ≤ β⁻ n → α ≤ lim β⁻
≤-lim′ zero β⁻ n x = tt
≤-lim′ (succ α) β⁻ n x = n , x
≤-lim′ (lim α⁻) β⁻ n x m = ≤-lim′ (α⁻ m) β⁻ n (x m) 
≤-lim′ (equinum α α₁ x₁ x₂ i) β⁻ n x = {!!}
≤-lim′ (ord-set α α₁ x₁ y i i₁) β⁻ n x = {!!}

≤-refl : ∀ α → α ≤ α
≤-refl = ord-to-prop (λ α → ≤-prop α α) tt id λ α⁻ H n → ≤-lim′ (α⁻ n) α⁻ n (H n)

≤-lim : ∀ α⁻ n → α⁻ n ≤ lim α⁻
≤-lim α⁻ n = ≤-lim′ (α⁻ n) α⁻ n (≤-refl (α⁻ n))

const-lim : (α : Ord) → lim (λ _ → α) ≡ α
const-lim α = equinum (lim λ _ → α) α (const (≤-refl α)) (≤-lim (const α) 0)
-}
