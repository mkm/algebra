{-# OPTIONS --cubical --erasure --guardedness --allow-unsolved-metas #-}
module Data.Circle where

open import Prelude hiding (succ)
open import Path.Comp
open import Path.Equiv
open import Control.Functor
open import Control.Monad
open import Data.Bool
open import Data.Int
open import Data.Truncation
open import Data.Show
open import Topology.Compact

data S¹ : Type where
  base : S¹
  loop : Ω₁ base

loop-at : (x : S¹) → x ≡ x
loop-at base = loop
loop-at (loop i) j = ■-square loop loop i j

_◆_ : S¹ → S¹ → S¹
base ◆ y = y
loop i ◆ y = loop-at y i

_◆′_ : {x : S¹} → Ω₁ base → Ω₁ x → Ω₁ x
(p ◆′ q) i = p i ◆ q i
-- _◆′_ : Ω₁ base → Ω₁ base → Ω₁ base
-- (p ◆′ q) i = p i ◆ q i

◆-comm : (x y : S¹) → x ◆ y ≡ y ◆ x
◆-comm base base = refl
◆-comm base (loop j) = refl
◆-comm (loop i) base = refl
◆-comm (loop i) (loop j) = refl

{-
◆-assoc : (x y z : S¹) → (x ◆ y) ◆ z ≡ x ◆ (y ◆ z)
◆-assoc base y z = refl
◆-assoc (loop i) base z = refl
◆-assoc (loop i) (loop j) z = the (■-square loop loop j i ◆ z ≡ loop-at (loop-at z j) i) {!!}
-}

loop-to-not : S¹ → Type
loop-to-not base = Bool
loop-to-not (loop i) = not-path i

refl-vs-loop : refl ≢ loop
refl-vs-loop p = false-vs-true λ i → transport (λ j → loop-to-not $ p i j) false

{-
S¹-base-connected : (x : S¹) → ∣ x ≡ base ∣₀
S¹-base-connected base = forget₀ refl
S¹-base-connected (loop i) =
  prop-fill collapse₀ i0 i (forget₀ λ j → loop (i ∨ j)) λ where
    (i = i0) → forget₀ refl
    (i = i1) → forget₀ refl

S¹-connected : (x y : S¹) → ∣ x ≡ y ∣₀
S¹-connected x y = do
  p ← S¹-base-connected x
  q ← S¹-base-connected y
  pure $ p ■ inv q

S¹-compact : Compact S¹
witness S¹-compact _ = base
universal S¹-compact f x α with inspect (f base)
universal S¹-compact f x α | false , p = absurd₀ $ do
  q ← S¹-connected base x
  let r = transport (λ i → f (q i) ≡ false) p
  pure ∘ uh-oh $ transport (λ i → So (r i)) α
universal S¹-compact f x α | true , p = transport (λ i → So (p (~ i))) oh 
-}

loop-action : Ω₁ base → S¹ → S¹
loop-action p base = base
loop-action p (loop i) = p i

loop-path : ∀ {ℓ} {A : Type ℓ} → (p : S¹ → A) → Ω₁ (p base)
loop-path p i = p (loop i)

loop-loop-equiv : ∀ {ℓ} (A : Type ℓ) → (S¹ → A) ≅ Σ A Ω₁
fun (loop-loop-equiv A) p = p base , λ i → p (loop i)
is-equiv (loop-loop-equiv A) = α
  where
    g : Σ A Ω₁ → S¹ → A
    g (x , p) base = x
    g (x , p) (loop i) = p i
    α : IsEquiv _
    linv α = g
    rinv α = g
    is-linv α i f base = f base
    is-linv α i f (loop j) = f (loop j)
    is-rinv α i (x , p) = x , p

loop-loop-path : ∀ {ℓ} (A : Type ℓ) → (S¹ → A) ≡ Σ A Ω₁
loop-loop-path A = equiv-path (loop-loop-equiv A)

{-
move-loop : {x : S¹} → Ω₁ base → Ω₁ x
move-loop p i = {!loop-action p (loop i)!}

to-loop : {x : S¹} → Ω₁ x → Ω₁ base
to-loop {x = base} p = p
to-loop {x = loop i} p j = {!p j!}

at-base : (S¹ → S¹) → Ω₁ base
at-base f = {!!}
-}

{-
at-base-is-equiv : IsEquiv at-base
linv at-base-is-equiv = _◆_
rinv at-base-is-equiv = _◆_
is-linv at-base-is-equiv i f base = ◆-comm (f base) base i
is-linv at-base-is-equiv i f (loop j) = {!!}
is-rinv at-base-is-equiv i x = ◆-comm x base i
-}

{-
functional-loops-equiv : Ω₁ (S¹ → S¹) ≅ Ω₁ S¹
functional-loops-equiv = {!!}

functional-loops : Ω₁ (S¹ → S¹) ≡ Ω₁ S¹
functional-loops i = {!!}
-}

reverse : S¹ → S¹
reverse base = base
reverse (loop i) = loop (~ i)

reverse-is-equiv : IsEquiv reverse
linv reverse-is-equiv = reverse
rinv reverse-is-equiv = reverse
is-linv reverse-is-equiv _ base = base
is-linv reverse-is-equiv _ (loop j) = loop j
is-rinv reverse-is-equiv _ base = base
is-rinv reverse-is-equiv _ (loop j) = loop j

reverse-equiv : S¹ ≅ S¹
fun reverse-equiv = reverse
is-equiv reverse-equiv = reverse-is-equiv

reverse-path : S¹ ≡ S¹
reverse-path = equiv-path reverse-equiv

loop-to-succ : S¹ → Type
loop-to-succ base = ℤ
loop-to-succ (loop i) = succ-path i

winding-number : Ω₁ base → ℤ
winding-number p = transport (λ i → loop-to-succ (p i)) (pos 0)

winding-number-at : (x : S¹) → Ω₁ x → ℤ
winding-number-at base = winding-number
winding-number-at (loop i) p = {!!}

partial-winding-number : (x y : S¹) → x ≡ y → ℤ
partial-winding-number base base p = winding-number p
partial-winding-number base (loop j) p = {!from-succ-path j $ transport (λ k → loop-to-succ (p k)) (pos 0)!}
partial-winding-number (loop i) base p = {!!}
partial-winding-number (loop i) (loop j) p = {!!}

loop^ : ℤ → Ω₁ base
loop^ (neg n) = inv (repeatᵣ n loop)
loop^ (pos n) = repeatᵣ n loop
loop^ (zero _) = refl

winding-repeat : ∀ n → winding-number (repeatᵣ n loop) ≡ pos n
winding-repeat 0 _ = pos 0
winding-repeat 1 i = hcomp-empty (pos 1) i
winding-repeat (Prelude.succ (Prelude.succ n)) =
  (shadow ∘ shadow ∘ succ ∘ succ ∘ winding-number ∘ repeatᵣ n $ loop) ■⟨ (λ i → shadow-id i ∘ shadow-id i ∘ succ ∘ succ ∘ winding-number ∘ repeatᵣ n $ loop) ⟩
  (succ ∘ succ $ winding-number (repeatᵣ n loop)) ■⟨ (λ i → succ ∘ succ $ winding-repeat n i) ⟩
  (succ ∘ succ $ pos n) ■⟨=⟩
  pos (Prelude.succ (Prelude.succ n)) ■⟨QED⟩

{-
winding-inv : ∀ n → winding-number (inv (repeatᵣ n loop)) ≡ negate (winding-number (repeatᵣ n loop))
winding-inv 0 = {!!}
winding-inv 1 = {!winding-inv n!}
winding-inv (Prelude.succ (Prelude.succ n)) = {!winding-inv n!}
-}

{-
winding-number-is-equiv : IsEquiv winding-number
linv winding-number-is-equiv = loop^
rinv winding-number-is-equiv = loop^
is-linv winding-number-is-equiv = {!!}
is-rinv winding-number-is-equiv i (neg n) = {!!}
{-
  where
    lemma : ∀ n → winding-number (repeatᵣ n (inv loop)) ≡ neg n
    lemma 0 i = zero (~ i)
    lemma 1 i = hcomp-empty (neg 1) i
    lemma (Prelude.succ (Prelude.succ n)) =
      (shadow ∘ shadow ∘ pred ∘ pred ∘ winding-number ∘ repeatᵣ n $ inv loop) ■⟨ (λ i → shadow-id i ∘ shadow-id i ∘ pred ∘ pred ∘ winding-number ∘ repeatᵣ n $ inv loop) ⟩
      (pred ∘ pred $ winding-number (repeatᵣ n $ inv loop)) ■⟨ (λ i → pred ∘ pred $ lemma n i) ⟩
      (pred ∘ pred $ neg n) ■⟨=⟩
      neg (Prelude.succ (Prelude.succ n)) ■⟨QED⟩
      -}
is-rinv winding-number-is-equiv i (pos n) = winding-repeat n i
is-rinv winding-number-is-equiv i (zero j) = {!!}

winding-number-equiv : Ω₁ base ≅ ℤ
fun winding-number-equiv = winding-number
is-equiv winding-number-equiv = winding-number-is-equiv

S¹-loop-space : Ω₁ base ≡ ℤ
S¹-loop-space = equiv-path winding-number-equiv
-}

{-
S¹-aut : Ω₁ S¹ ≅ Bool
fun S¹-aut p = {!path λ i → transport p (loop i)!}
is-equiv S¹-aut = {!!}
-}

{-
instance
  S¹-show : Show S¹
  show ⦃ S¹-show ⦄ _ = "base"

  S¹-loop-show : ShowLoop S¹
  show-loop ⦃ S¹-loop-show ⦄ p = "loop^ " ++ show (winding-number-at _ p)
-}
