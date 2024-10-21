{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Maybe where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Path.Equiv.Univalence
open import Data.Nat
open import Data.Nat.Countable
open import Data.Truncation

data Maybe {ℓ} (A : Type ℓ) : Type ℓ where
  nothing : Maybe A
  just : A → Maybe A

from-maybe : ∀ {ℓ} {A : Type ℓ} → A → Maybe A → A
from-maybe x nothing = x
from-maybe _ (just x) = x

nothing-vs-just : ∀ {ℓ} {A : Type ℓ} {x : A} → nothing ≢ just x
nothing-vs-just p = transport (λ i → T (p i)) tt
  where
    T : Maybe _ → Type
    T nothing = ⊤
    T (just _) = ⊥

just-inj : ∀ {ℓ} {A : Type ℓ} {x y : A} → just x ≡ just y → x ≡ y
just-inj {x = x} p i = from-maybe x (p i)

Maybes : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
Maybes zero A = A
Maybes (succ n) A = Maybe (Maybes n A)

maybe-inj : ∀ {ℓ} {A B : Type ℓ} → Maybe A ≡ Maybe B → A ≡ B
maybe-inj {A = A} {B = B} p = equiv-path α
  where
    μ : ∀ {ℓ} {A B : Type ℓ} (p : Maybe A ≡ Maybe B) → A → B
    μ p a with inspect $ transport p (just a)
    μ p a | nothing , q with inspect $ transport p nothing
    μ p a | nothing , q | nothing , r = absurd $ nothing-vs-just (transport-inj₂ p nothing (just a) (r ■ inv q))
    μ p a | nothing , q | just b , r = b
    μ p a | just b , q = b

    μ-inv′ : ∀ {ℓ} {A B : Type ℓ} (p : Maybe A ≡ Maybe B) (a : A) (b : B) (c : A) → μ p a ≡ b → μ (inv p) b ≡ c → a ≡ c
    μ-inv′ p a b c q r with inspect $ transport p (just a)
    μ-inv′ p a b c q r | nothing , s with inspect $ transport p nothing
    μ-inv′ p a b c q r | nothing , s | nothing , t = absurd $ nothing-vs-just (transport-inj₂ p nothing (just a) (t ■ inv s))
    μ-inv′ p a b c q r | nothing , s | just b′ , t with inspect $ transport (inv p) (just b)
    μ-inv′ p a b c q r | nothing , s | just b′ , t | nothing , u with inspect $ transport (inv p) nothing
    μ-inv′ p a b c q r | nothing , s | just b′ , t | nothing , u | nothing , v =
      absurd $ nothing-vs-just (transport-inj₂ (inv p) nothing (just b) (v ■ inv u))
    μ-inv′ p a b c q r | nothing , s | just b′ , t | nothing , u | just c′ , v =
      just-inj $ (λ i → transport-inv p (~ i) (just a)) ■ ap (transport (inv p)) s ■ v ■ ap just r 
    μ-inv′ p a b c q r | nothing , s | just b′ , t | just c′ , u =
      absurd $ nothing-vs-just ((λ i → transport-inv p (~ i) nothing) ■ ap (transport (inv p)) t ■ ap (transport (inv p) ∘ just) q ■ u)
    μ-inv′ p a b c q r | just b′ , s with inspect $ transport (inv p) (just b)
    μ-inv′ p a b c q r | just b′ , s | nothing , t =
      absurd $ nothing-vs-just (inv t ■ ap (transport (inv p)) (ap just (inv q) ■ inv s) ■ λ i → transport-inv p i (just a))
    μ-inv′ p a b c q r | just b′ , s | just c′ , t =
      just-inj $ (λ i → transport-inv p (~ i) (just a)) ■ ap (transport (inv p)) (s ■ ap just q) ■ t ■ ap just r

    μ-inv : ∀ {ℓ} {A B : Type ℓ} (p : Maybe A ≡ Maybe B) → μ (inv p) ∘ μ p ≡ id
    μ-inv p i a = μ-inv′ p a (μ p a) (μ (inv p) (μ p a)) refl refl (~ i)

    α : A ≅ B
    fun α = μ p
    linv (is-equiv α) = μ (inv p)
    rinv (is-equiv α) = μ (inv p)
    is-linv (is-equiv α) = μ-inv p
    is-rinv (is-equiv α) = μ-inv (inv p)

maybe-set : ∀ {ℓ} {A : Type ℓ} → IsSet A → IsSet (Maybe A)
maybe-set {A = A} 𝒜 nothing nothing p q i j = along (p j) (q j) (between i0 j p) (between i0 j q) i
  where
    along : (pⱼ qⱼ : Maybe A) → nothing ≡ pⱼ → nothing ≡ qⱼ → pⱼ ≡ qⱼ
    along nothing nothing _ _ = refl
    {-# CATCHALL #-}
    along pⱼ qⱼ p₀ⱼ q₀ⱼ = inv p₀ⱼ ■ q₀ⱼ
maybe-set 𝒜 nothing (just y) p q = absurd $ nothing-vs-just p
maybe-set 𝒜 (just x) nothing p q = absurd $ nothing-vs-just (inv p)
maybe-set {A = A} 𝒜 (just x) (just y) p q i j = along (p j) (q j) (between i0 j p) (between i0 j q) (λ i → 𝒜 x y (ap unjust p) (ap unjust q) i j) i 
  where
    unjust : Maybe A → A
    unjust = from-maybe x
    along : (pⱼ qⱼ : Maybe A) → just x ≡ pⱼ → just x ≡ qⱼ → unjust pⱼ ≡ unjust qⱼ → pⱼ ≡ qⱼ
    along (just pⱼ) (just qⱼ) _ _ α = ap just α
    {-# CATCHALL #-}
    along pⱼ qⱼ p₀ⱼ q₀ⱼ α = inv p₀ⱼ ■ q₀ⱼ

maybe-countable : ∀ {ℓ} {A : Type ℓ} → Countable A → Countable (Maybe A)
maybe-countable {A = A} = map-∣∣₀ e
  where
    module _ (α : A ≅ ℕ) where
      f : Maybe A → ℕ
      f nothing = zero
      f (just x) = succ $ fun α x
      g : ℕ → Maybe A
      g zero = nothing
      g (succ n) = just $ linv (is-equiv α) n
      gf : g ∘ f ≡ id
      gf _ nothing = nothing
      gf i (just x) = just $ is-linv (is-equiv α) i x
      fg : f ∘ g ≡ id
      fg _ zero = zero
      fg i (succ n) = succ $ linv-is-rinv (is-equiv α) i n
      e : Maybe A ≅ ℕ
      fun e = f
      linv (is-equiv e) = g
      rinv (is-equiv e) = g
      is-linv (is-equiv e) = gf
      is-rinv (is-equiv e) = fg
