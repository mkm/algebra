{-# OPTIONS --cubical --erasure --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Data.Fin where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Control.Monad
open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.Sigma
open import Data.Decision
open import Data.Truncation
open import Data.Truncation.Equiv

data Fin : ℕ → Type where
  fzero : ∀ {n} → Fin (succ n)
  fsucc : ∀ {n} → Fin n → Fin (succ n)

no-fin-zero : ¬ (Fin 0)
no-fin-zero ()

fzero-vs-fsucc : ∀ {n} {a : Fin n} → fzero ≢ fsucc a
fzero-vs-fsucc p = transport (λ i → T (p i)) tt
  where
    T : ∀ {n} → Fin n → Type
    T fzero = ⊤
    T (fsucc _) = ⊥

fin : ∀ m {n} → Fin (succ (m + n))
fin zero = fzero
fin (succ m) = fsucc (fin m)

unfin : ∀ {n} → Fin n → ℕ
unfin fzero = zero
unfin (fsucc k) = succ (unfin k)

reduce-fin : ∀ {ℓ} {A : Type ℓ} n → A → (Fin n → A → A) → A
reduce-fin zero k f = k
reduce-fin (succ n) k f = f fzero (reduce-fin n k λ m → f (fsucc m))

fin-zero : Fin zero ≡ ⊥
fin-zero = ⊥-path no-fin-zero

fin-succ-equiv : ∀ n → Fin (succ n) ≅ Maybe (Fin n)
fin-succ-equiv n =
  λ where
    .fun → f
    .is-equiv .linv → g
    .is-equiv .rinv → g
    .is-equiv .is-linv → gf
    .is-equiv .is-rinv → fg
  where
    f : Fin (succ n) → Maybe (Fin n)
    f fzero = nothing
    f (fsucc n) = just n
    g : Maybe (Fin n) → Fin (succ n)
    g nothing = fzero
    g (just n) = fsucc n
    gf : g ∘ f ≡ id
    gf _ fzero = fzero
    gf _ (fsucc n) = fsucc n
    fg : f ∘ g ≡ id
    fg _ nothing = nothing
    fg _ (just n) = just n

fin-succ : ∀ n → Fin (succ n) ≡ Maybe (Fin n)
fin-succ n = equiv-path (fin-succ-equiv n)

fin-maybes : ∀ n → Fin n ≡ Maybes n ⊥
fin-maybes zero = fin-zero
fin-maybes (succ n) = fin-succ n ■ ap Maybe (fin-maybes n)

fin-inj : ∀ m n → Fin m ≡ Fin n → m ≡ n
fin-inj zero zero p = refl
fin-inj zero (succ n) p = absurd $ no-fin-zero (transport (inv p) fzero)
fin-inj (succ m) zero p = absurd $ no-fin-zero (transport p fzero)
fin-inj (succ m) (succ n) p =
  ap succ (fin-inj m n (maybe-inj (transport (λ t → fin-succ m t ≡ fin-succ n t) p)))

Finite : ∀ {ℓ} → Type ℓ → Type ℓ
Finite A = Σ ℕ λ n → A ≅₀ Fin n

finite-prop : ∀ {ℓ} (A : Type ℓ) → IsProp (Finite A)
finite-prop A (m , α) (n , β) = Σ-path (recall₀ (ℕ-set m n) p) (propₚ _ collapse₀ α β)
  where
    p : ∣ m ≡ n ∣₀
    p = do
      α′ ← α
      β′ ← β
      pure $ fin-inj m n (equiv-path (≅-inv α′ ≅-∘ β′))

bool-finite : Finite Bool
bool-finite = 2 , forget₀ e
  where
    e : Bool ≅ Fin 2
    fun e false = fzero
    fun e true = fsucc fzero
    linv (is-equiv e) fzero = false
    linv (is-equiv e) (fsucc fzero) = true
    rinv (is-equiv e) fzero = false
    rinv (is-equiv e) (fsucc fzero) = true
    is-linv (is-equiv e) _ false = false
    is-linv (is-equiv e) _ true = true
    is-rinv (is-equiv e) _ fzero = fzero
    is-rinv (is-equiv e) _ (fsucc fzero) = fsucc fzero

Σ-finite : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} → Finite A → ((x : A) → Finite (B x)) → Finite (Σ A B)
Σ-finite (n , α) B-fin = {! !}
  where
    card : ∣ ℕ ∣₀
    card = do
      α′ ← α
      pure $ reduce-fin n 0 λ m c → fst (B-fin (linv (is-equiv α′) m)) + c

{-
fsucc-inj : ∀ {n} {a b : Fin n} → fsucc a ≡ fsucc b → a ≡ b
fsucc-inj {n = n} {a = a} {b = b} p = {!!}
  where
    T : Fin (succ n) → Type
    T fzero = {!!}
    T (fsucc a) = {!!}

fin-inj : ∀ m n → Fin m ≡ Fin n → m ≡ n
fin-inj zero zero p = refl
fin-inj zero (succ n) p = absurd $ transport (λ t → ¬ (p t)) no-fin-zero fzero
fin-inj (succ m) zero p = absurd $ transport (λ t → ¬ (p (~ t))) no-fin-zero fzero
fin-inj (succ m) (succ n) p = ap succ $ fin-inj m n (equiv-path α)
  where
    μ : ∀ {m n} → Fin (succ m) ≡ Fin (succ n) → Fin m → Fin n
    μ p a with inspect $ transport p (fsucc a)
    μ p a | fzero , _ with inspect $ transport p fzero
    μ p a | fzero , q | fzero , r = absurd $ fzero-vs-fsucc (transport-inj₂ p fzero (fsucc a) (r ■ inv q))
    μ p a | fzero , _ | fsucc b , _ = b
    μ p a | fsucc b , _ = b
    μ-inv′ : ∀ {m n} (p : Fin (succ m) ≡ Fin (succ n)) (a : Fin m) (b : Fin n) (c : Fin m) → μ p a ≡ b → μ (inv p) b ≡ c → a ≡ c
    μ-inv′ p a b c q r with inspect $ transport p (fsucc a)
    μ-inv′ p a b c q r | fzero , s with inspect $ transport p fzero
    μ-inv′ p a b c q r | fzero , s | fzero , t = absurd $ fzero-vs-fsucc (transport-inj₂ p fzero (fsucc a) (t ■ inv s))
    μ-inv′ p a b c q r | fzero , s | fsucc b′ , t with inspect $ transport (inv p) (fsucc b)
    μ-inv′ p a b c q r | fzero , s | fsucc b′ , t | fzero , u with inspect $ transport (inv p) fzero
    μ-inv′ p a b c q r | fzero , s | fsucc b′ , t | fzero , u | fzero , v =
      absurd $ fzero-vs-fsucc (transport-inj₂ (inv p) fzero (fsucc b) (v ■ inv u))
    μ-inv′ p a b c q r | fzero , s | fsucc b′ , t | fzero , u | fsucc c′ , v =
      fsucc-inj $
        fsucc a ■⟨ (λ i → transport-inv p (~ i) (fsucc a)) ⟩
        transport (inv p) (transport p (fsucc a)) ■⟨ (λ i → transport (inv p) (s i)) ⟩
        transport (inv p) fzero ■⟨ v ⟩
        fsucc c′ ■⟨ (λ i → fsucc (r i)) ⟩
        fsucc c ■⟨QED⟩
    μ-inv′ p a b c q r | fzero , s | fsucc b′ , t | fsucc c′ , u =
      absurd $ fzero-vs-fsucc ((λ i → transport-inv p (~ i) fzero) ■ (λ i → transport (inv p) (t i)) ■ (λ i → transport (inv p) (fsucc (q i))) ■ u) 
    μ-inv′ p a b c q r | fsucc b′ , s with inspect $ transport (inv p) (fsucc b)
    μ-inv′ p a b c q r | fsucc b′ , s | fzero , t =
      absurd $ fzero-vs-fsucc (inv t ■ (λ i → transport (inv p) (fsucc (q (~ i)))) ■ (λ i → transport (inv p) (s (~ i))) ■ λ i → transport-inv p i (fsucc a))
    μ-inv′ p a b c q r | fsucc b′ , s | fsucc c′ , t =
      fsucc-inj $
        fsucc a ■⟨ (λ i → transport-inv p (~ i) (fsucc a)) ⟩
        transport (inv p) (transport p (fsucc a)) ■⟨ (λ i → transport (inv p) (s i)) ⟩
        transport (inv p) (fsucc b′) ■⟨ (λ i → transport (inv p) (fsucc (q i))) ⟩
        transport (inv p) (fsucc b) ■⟨ t ⟩
        fsucc c′ ■⟨ (λ i → fsucc (r i)) ⟩
        fsucc c ■⟨QED⟩

    μ-inv : ∀ {m n} (p : Fin (succ m) ≡ Fin (succ n)) → μ (inv p) ∘ μ p ≡ id
    μ-inv p i a = μ-inv′ p a (μ p a) (μ (inv p) (μ p a)) refl refl (~ i)
    α : Fin m ≅ Fin n
    fun α = μ p
    linv (is-equiv α) = μ (inv p)
    rinv (is-equiv α) = μ (inv p)
    is-linv (is-equiv α) = μ-inv p
    is-rinv (is-equiv α) = μ-inv (inv p)
-}
