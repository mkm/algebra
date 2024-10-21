{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Segment where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Path.Strict
open import Data.Truncation
open import Data.Circle

data Seg : Type where
  s0 : Seg
  s1 : Seg
  seg : s0 ≡ s1

at-seg : {A : Type} {x y : A} → x ≡ y → Seg → A
at-seg p s0 = p i0
at-seg p s1 = p i1
at-seg p (seg i) = p i

seg-prop : IsProp Seg
seg-prop s0 s0 = refl
seg-prop s0 s1 = seg
seg-prop s0 (seg j) = λ k → seg (j ∧ k)
seg-prop s1 s0 = inv seg
seg-prop s1 s1 = refl
seg-prop s1 (seg j) = λ k → seg (j ∨ ~ k)
seg-prop (seg i) s0 = λ k → seg (i ∧ ~ k)
seg-prop (seg i) s1 = λ k → seg (i ∨ k)
seg-prop (seg i) (seg j) = λ k → seg ((i ∧ ~ k) ∨ (j ∧ k) ∨ (i ∧ j))

path-unify : ↑ s0 ＝ ↑ s1 → {A : Type} {x y : A} → x ≡ y → ↑ x ＝ ↑ y
path-unify H {A = A} p = apₛ (λ x → ↑ (at-seg p (↓ x))) H

s0-vs-s1 : ↑ s0 ＝ ↑ s1 → ⊥
s0-vs-s1 H = refl-vs-loop uip′
  where
    r : (s : base ≡ base) → unify-path (path-unify H s) ≡ refl
    r s with path-unify H {x = base} s
    r s | unify = refl
    q : unify-path (path-unify H loop) ≡ loop
    q = transport (λ i → unify-path (path-unify H (λ j → loop (i ∧ j))) ≡ (λ j → loop (i ∧ j))) (r refl)
    uip′ : refl ≡ loop
    uip′ = inv (r loop) ■ q

seg-vs-⊤ : ↑ ⊤ ＝ ↑ Seg → ⊥
seg-vs-⊤ p = s0-vs-s1 (transportₛ T p (λ { tt tt → unify }) s0 s1)
  where
    T : ◆ Type → SSet
    T A = (x y : ↓ A) → ↑ x ＝ ↑ y

seg-⊤ : Seg ≡ ⊤
seg-⊤ = equiv-path α
  where
    α : Seg ≅ ⊤
    fun α _ = tt
    linv (is-equiv α) _ = s0
    rinv (is-equiv α) _ = s1
    is-linv (is-equiv α) i s0 = s0
    is-linv (is-equiv α) i s1 = seg i
    is-linv (is-equiv α) i (seg j) = seg (i ∧ j)
    is-rinv (is-equiv α) _ _ = tt

data ℕₛ : ℕ → SSet where
  zeroₛ : ℕₛ zero
  succₛ : ∀ {n} → ℕₛ n → ℕₛ (succ n)

open import Data.Nat
_+ₛ_ : ∀ {m n} → ℕₛ m → ℕₛ n → ℕₛ (m + n)
zeroₛ +ₛ n = n
succₛ m +ₛ n = succₛ (m +ₛ n)

{-
+ₛ-zero : ∀ {n} (nₛ : ℕₛ n) → (nₛ +ₛ zeroₛ) ＝ nₛ
+ₛ-zero nₛ = ?
-}
