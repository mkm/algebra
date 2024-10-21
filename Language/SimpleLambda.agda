{-# OPTIONS --cubical --erasure --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Language.SimpleLambda where

open import Prelude
open import Path.Comp
open import Data.Fin
open import Data.Vec hiding (drop)
open import Data.Truncation

data Ty : Type where
  * : Ty
  _⇒_ : Ty → Ty → Ty

Env : ℕ → Type
Env = Vec Ty

private
  variable
    τ τ′ τ₁ τ₂ : Ty
    m n : ℕ

lookup : Env n → Fin n → Ty
lookup (τ ∷ _) fzero = τ
lookup (_ ∷ Γ) (fsucc x) = lookup Γ x

data _⊆_ : Env m → Env n → Type where
  empty : [] ⊆ []
  drop : {Γ : Env m} {Γ′ : Env n} (τ : Ty) → Γ ⊆ Γ′ → Γ ⊆ τ ∷ Γ′
  keep : {Γ : Env m} {Γ′ : Env n} (τ : Ty) → Γ ⊆ Γ′ → τ ∷ Γ ⊆ τ ∷ Γ′

infix 10 _⊆_

id-sub : (Γ : Env n) → Γ ⊆ Γ
id-sub [] = empty
id-sub (τ ∷ Γ) = keep τ (id-sub Γ)

empty-sub : (Γ : Env n) → [] ⊆ Γ
empty-sub [] = empty
empty-sub (τ ∷ Γ) = drop τ (empty-sub Γ)

data Partition : ∀ {m₁ m₂} {Γ₁ : Env m₁} {Γ₂ : Env m₂} {Γ : Env n} → Γ₁ ⊆ Γ → Γ₂ ⊆ Γ → Type where
  empty : Partition empty empty
  drop-keep : ∀ {m₁ m₂} {Γ₁ : Env m₁} {Γ₂ : Env m₂} {Γ : Env n} (τ : Ty) (ρ₁ : Γ₁ ⊆ Γ) (ρ₂ : Γ₂ ⊆ Γ)
    → Partition ρ₁ ρ₂ → Partition (drop τ ρ₁) (keep τ ρ₂)
  keep-drop : ∀ {m₁ m₂} {Γ₁ : Env m₁} {Γ₂ : Env m₂} {Γ : Env n} (τ : Ty) (ρ₁ : Γ₁ ⊆ Γ) (ρ₂ : Γ₂ ⊆ Γ)
    → Partition ρ₁ ρ₂ → Partition (keep τ ρ₁) (drop τ ρ₂)

data Exp (Γ : Env n) : Ty → Type
data _∼_ {Γ : Env n} {τ} : Exp Γ τ → Exp Γ τ → Type
data Subst : (Γ : Env m) (Γ′ : Env n) → Type

{-# TERMINATING #-}
subst : {Γ : Env m} {Γ′ : Env n} → Subst Γ Γ′ → Exp Γ τ → Exp Γ′ τ

data Exp {n} Γ where
  var : (x : Fin n) → lookup Γ x ≡ τ → Exp Γ τ
  lam : ∀ τ₁ → Exp (τ₁ ∷ Γ) τ₂ → Exp Γ (τ₁ ⇒ τ₂)
  app : Exp Γ (τ′ ⇒ τ) → Exp Γ τ′ → Exp Γ τ
  coe : τ′ ≡ τ → Exp Γ τ′ → Exp Γ τ
  conv : {e e′ : Exp Γ τ} → e ∼ e′ → e ≡ e′
  exp-set : IsSet (Exp Γ τ)

data Subst where
  empty : Subst [] []
  weak : {Γ : Env m} {Γ′ : Env n} (τ : Ty) → Subst Γ Γ′ → Subst Γ (τ ∷ Γ′)
  keep : {Γ : Env m} {Γ′ : Env n} (τ : Ty) → Subst Γ Γ′ → Subst (τ ∷ Γ) (τ ∷ Γ′)
  replace : {Γ : Env m} {Γ′ : Env n} {τ : Ty} (e : Exp Γ′ τ) → Subst Γ Γ′ → Subst (τ ∷ Γ) Γ′

{-
  sb-empty : Subst empty
  sb-keep : {Γ : Env m} {Γ′ : Env n} {ρ : Γ ⊆ Γ′} (τ : Ty) → Subst ρ → Subst (keep τ ρ)
  sb-replace : {Γ : Env m} {Γ′ : Env n} {ρ : Γ ⊆ Γ′} {τ : Ty} (e : Exp Γ τ) → Subst ρ → Subst (drop τ ρ)
-}

id-subst : (Γ : Env n) → Subst Γ Γ
id-subst [] = empty
id-subst (τ ∷ Γ) = keep τ (id-subst Γ)

data _∼_ {n} {Γ} {τ} where
  β-red : (e₁ : Exp (τ′ ∷ Γ) τ) (e₂ : Exp Γ τ′)
    → app (lam τ′ e₁) e₂ ∼ subst (replace e₂ (id-subst Γ)) e₁

{-
-- transport-exp : {Γ : Env n} → τ ≡ τ′ → Exp Γ τ → Exp Γ τ′
transport-sub : {Γ₁ Γ₂ : Env m} {Γ₁′ Γ₂′ : Env n} → Γ₁ ≡ Γ₂ → Γ₁′ ≡ Γ₂′ → Γ₁ ⊆ Γ₁′ → Γ₂ ⊆ Γ₂′
transport-sub p q = transport (λ t → p t ⊆ q t)

transport-exp-subst : {Γ : Env m} {Γ′ Γ″ : Env n} {ρ : Γ′ ⊆ Γ} (σ : Subst ρ) (p : τ ≡ τ′) (e : Exp Γ τ)
  → transport-exp p (subst σ e) ≡ subst σ (transport-exp p e)
-}

{-
transport-exp {Γ = Γ} p (var x r) = var x (r ■ p)
transport-exp p (lam τ₁ e r) = lam τ₁ (transport-exp refl e) (r ■ p)
transport-exp p (app {τ′ = τ₀} e₁ e₂) = app (transport-exp (λ i → τ₀ ⇒ p i) e₁) (transport-exp refl e₂)
transport-exp {Γ = Γ} p (conv (β-red e₁ e₂) i) =
  ({! conv (β-red (lam _ (transport-exp refl e₁) (refl ■ refl)) (transport-exp refl e₂))  !} ■ inv (transport-exp-subst (sb-replace e₂ (sb-id Γ)) p e₁)) i
transport-exp p (exp-set e e′ q r i j) =
  exp-set (transport-exp p e) (transport-exp p e′) (λ j → transport-exp p (q j)) (λ j → transport-exp p (r j)) i j
-}

subst-tail : {Γ : Env m} {Γ′ : Env n} {τ : Ty} → Subst (τ ∷ Γ) Γ′ → Subst Γ Γ′
subst-tail (weak τ′ σ) = weak τ′ (subst-tail σ)
subst-tail (keep τ′ σ) = weak τ′ σ
subst-tail (replace _ σ) = σ

sub-subst : ∀ {k} {Γ : Env m} {Γ′ : Env n} {Γ″ : Env k} → Γ ⊆ Γ′ → Subst Γ′ Γ″ → Subst Γ Γ″
sub-subst empty σ = ?
sub-subst (drop τ ρ) σ = sub-subst ρ (subst-tail σ)
sub-subst (keep τ ρ) (weak τ′ σ) = weak τ′ (sub-subst (keep τ ρ) σ)
sub-subst (keep τ ρ) (keep .τ σ) = keep τ (sub-subst ρ σ)
sub-subst (keep τ ρ) (replace e σ) = replace e (sub-subst ρ σ)

weaken-var : {Γ : Env m} {Γ′ : Env n} → Γ ⊆ Γ′ → Fin m → Fin n
weaken-var empty x = x
weaken-var (keep τ ρ) fzero = fzero
weaken-var (keep τ ρ) (fsucc x) = fsucc (weaken-var ρ x)
weaken-var (drop τ ρ) x = fsucc (weaken-var ρ x)

weaken-var-lookup : {Γ : Env m} {Γ′ : Env n} (ρ : Γ ⊆ Γ′) (x : Fin m) → lookup Γ′ (weaken-var ρ x) ≡ lookup Γ x
weaken-var-lookup (keep τ ρ) fzero = refl
weaken-var-lookup (keep τ ρ) (fsucc x) = weaken-var-lookup ρ x
weaken-var-lookup (drop τ ρ) x = weaken-var-lookup ρ x

{-
weaken-compose : ∀ {k} {Γ : Env m} {Γ′ : Env n} {Γ″ : Env k} → Γ′ ⊆ Γ″ → Γ ⊆ Γ′ → Γ ⊆ Γ″
weaken-compose empty ρ′ = ρ′
weaken-compose (keep τ ρ) (keep .τ ρ′) = keep τ (weaken-compose ρ ρ′)
weaken-compose (keep τ ρ) (drop τ′ ρ′) = drop τ (weaken-compose ρ ρ′)
weaken-compose (drop τ ρ) ρ′ = drop τ (weaken-compose ρ ρ′)

weaken-subst : ∀ {k} {Γ : Env m} {Γ′ : Env n} {Γ″ : Env k} {ρ : Γ ⊆ Γ′} (ρ′ : Γ′ ⊆ Γ″) → Subst ρ → Subst (weaken-compose ρ′ ρ)
-- wrong, cannot just weaken substitution domain
{-
weaken-of-subst : ∀ {k} {Γ : Env m} {Γ′ : Env n} {Γ″ : Env k} {ρ : Γ ⊆ Γ′} (ρ′ : Γ′ ⊆ Γ″) (σ : Subst ρ) (e : Exp Γ′ τ)
  → weaken ρ′ (subst σ e) ≡ subst (weaken-subst ρ′ σ) (weaken ρ′ e)
-}
weakened-subst : ∀ {k} {Γ : Env m} {Γ′ : Env n} {Γ″ : Env k} {ρ : Γ ⊆ Γ′} (ρ′ : Γ′ ⊆ Γ″) (σ : Subst ρ) (e : Exp Γ′ τ)
  → subst (weaken-subst ρ′ σ) (weaken ρ′ e) ≡ subst σ e

-}

weaken : {Γ : Env m} {Γ′ : Env n} → Γ ⊆ Γ′ → Exp Γ τ → Exp Γ′ τ

subst-of-weaken : ∀ {k} {Γ : Env m} {Γ′ : Env n} {Γ″ : Env k} (ρ : Γ ⊆ Γ′) (σ : Subst Γ′ Γ″) (e : Exp Γ τ)
  → subst σ (weaken ρ e) ≡ subst (sub-subst ρ σ) e

relax : ∀ {k} {Γ : Env m} {Γ′ : Env n} {Γ″ : Env k} → Γ′ ⊆ Γ″ → Subst Γ Γ′ → Subst Γ Γ″

sub-subst-id : {Γ : Env m} {Γ′ : Env n} (ρ : Γ ⊆ Γ′) → sub-subst ρ (id-subst Γ′) ≡ relax ρ (id-subst Γ)

weaken ρ (var x p) = var (weaken-var ρ x) (weaken-var-lookup ρ x ■ p)
weaken ρ (lam τ₁ e) = lam τ₁ (weaken (keep τ₁ ρ) e)
weaken ρ (app e₁ e₂) = app (weaken ρ e₁) (weaken ρ e₂)
weaken ρ (coe p e) = coe p (weaken ρ e)
weaken ρ (conv (β-red {τ′ = τ′} e₁ e₂) i) = {! p i !}
  where
    p : app (weaken ρ (lam τ′ e₁)) (weaken ρ e₂) ≡ weaken ρ (subst (replace e₂ (id-subst _)) e₁)
    p =
      app (weaken ρ (lam τ′ e₁)) (weaken ρ e₂)
        ■⟨=⟩
      app (lam τ′ (weaken (keep τ′ ρ) e₁)) (weaken ρ e₂)
        ■⟨ conv (β-red (weaken (keep τ′ ρ) e₁) (weaken ρ e₂)) ⟩
      subst (replace (weaken ρ e₂) (id-subst _)) (weaken (keep τ′ ρ) e₁)
        ■⟨ subst-of-weaken (keep τ′ ρ) (replace (weaken ρ e₂) (id-subst _)) e₁ ⟩
      subst (replace (weaken ρ e₂) (sub-subst ρ (id-subst _))) e₁
        ■⟨ {! !} ⟩
      weaken ρ (subst (replace e₂ (id-subst _)) e₁) ■⟨QED⟩
weaken ρ (exp-set e e′ p q i j) =
  exp-set (weaken ρ e) (weaken ρ e′) (λ j → weaken ρ (p j)) (λ j → weaken ρ (q j)) i j

relax empty σ = σ
relax (drop τ ρ) σ = weak τ (relax ρ σ)
relax (keep τ ρ) (weak .τ σ) = weak τ (relax ρ σ)
relax (keep τ ρ) (keep .τ σ) = keep τ (relax ρ σ)
relax ρ@(keep _ _) (replace e σ)  = replace (weaken ρ e) (relax ρ σ)

sub-subst-id empty = refl
sub-subst-id (drop τ ρ) = {! sub-subst-id ρ !}
sub-subst-id (keep τ ρ) = {! !}

subst-var : {Γ : Env m} {Γ′ : Env n} → Subst Γ Γ′ → (x : Fin m) → Exp Γ′ (lookup Γ x)
subst-var (weak τ′ σ) x = weaken (drop τ′ (id-sub _)) $ subst-var σ x
subst-var (keep _ σ) fzero = var fzero refl
subst-var (keep τ′ σ) (fsucc x) = weaken (drop τ′ (id-sub _)) (subst-var σ x)
subst-var (replace e σ) fzero = e
subst-var (replace e σ) (fsucc x) = subst-var σ x

subst σ (var x p) = coe p $ subst-var σ x
subst σ (lam τ₁ e) = lam τ₁ (subst (keep τ₁ σ) e)
subst σ (app e₁ e₂) = app (subst σ e₁) (subst σ e₂)
subst σ (coe p e) = coe p (subst σ e)
subst σ (conv _ i) = {! !}
subst σ (exp-set e e′ p q i j) =
  exp-set (subst σ e) (subst σ e′) (λ j → subst σ (p j)) (λ j → subst σ (q j)) i j

subst-of-weaken ρ σ (var x p) = {! !}
subst-of-weaken ρ σ (lam τ₁ e) = {! !}
subst-of-weaken ρ σ (app e₁ e₂) = {! !}
subst-of-weaken ρ σ (coe p e) = {! !}
subst-of-weaken ρ σ (conv _ i) j = {! !}
subst-of-weaken ρ σ (exp-set e e′ p q i j) = {! !}

-- Γ = τ₁ ∷ τ₂ ∷ []
-- σ = keep τ₁ (replace v [])
-- e = (var f0 _ , var f1 _)
--
-- subst σ e = (subst-var σ f0 , subst-var σ f1) = (var f0 _ , weaken _ v)

{-
weaken-subst ρ′ sb-empty  = {! !}
weaken-subst ρ′ (sb-keep τ σ)  = {! !}
weaken-subst ρ′ (sb-replace e σ)  = {! !}
-}

-- weaken-of-subst = ?

{-
data Exp {n} (Γ : Env n) : Ty → Type
data Can {n} {Γ : Env n} : (τ : Ty) → Exp Γ τ → Type

subst : ∀ {n} {Γ : Env n} → Exp Γ τ′ → Exp (τ′ ∷ Γ) τ → Exp Γ τ

data Exp {n} Γ where
  # : (x : Fin n) → Γ !! x ≡ τ → Exp Γ τ
  ‵λ : Exp (τ ∷ Γ) τ′ → Exp Γ (τ ⇒ τ′)
  _‵$_ : Exp Γ (τ′ ⇒ τ) → Exp Γ τ′ → Exp Γ τ
  β : {e₁ : Exp (τ′ ∷ Γ) τ} {e₂ : Exp Γ τ′}
    → Can τ e₁ → Can τ′ e₂
    → ‵λ e₁ ‵$ e₂ ≡ subst e₂ e₁

data Can {n} {Γ} where
  #ᶜ : (x : Fin n) (α : Γ !! x ≡ *) → Can * (# x α)
  ‵λᶜ : {e : Exp (τ ∷ Γ) τ′} → Can τ′ e → Can (τ ⇒ τ′) (‵λ e)
  ‵$ᶜ : {x : Fin n} {α : Γ !! x ≡ τ′ ⇒ τ} {e : Exp Γ τ′} → Can τ′ e → Can τ (# x α ‵$ e)

subst = {!!}
-}
