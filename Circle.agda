{-# OPTIONS --cubical --prop #-}
module Circle where

open import Path
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Logic
open import Nat as N
open import Int as Z
open import String
open import Show

data S¹ : Type where
  base : S¹
  loop : base ≡ base

code : S¹ → Type
code base = ℤ
code (loop i) = succ-path i

encode : base ≡ base → ℤ
encode p = transport (i ⊢ code (p i)) (pos 0)

decode : ℤ → base ≡ base
decode n = Z.iterate-path n loop

{-
encode-decode-nat : ∀ n → encode (N.iterate-path n loop) ≡ pos n
encode-decode-nat zero _ = pos 0
encode-decode-nat (ℕ.succ n) = {!!}

encode-decode : ∀ n → encode (decode n) ≡ n
encode-decode (pos n) = {!!}
encode-decode (neg n) = {!!}
encode-decode (zero i) = {!!}
-}

loop-nontriv : loop ≢ id
loop-nontriv p = zero≢succ (inv (pos-inj (cong encode p))) 

flip : S¹ ≡ S¹
flip = univ (isoToEquiv φ)
  where
    φ : Iso S¹ S¹
    Iso.fun φ base = base
    Iso.fun φ (loop i) = loop (~ i)
    Iso.inv φ base = base
    Iso.inv φ (loop i) = loop (~ i)
    Iso.rightInv φ base = id
    Iso.rightInv φ (loop i) = id
    Iso.leftInv φ base = id
    Iso.leftInv φ (loop i) = id

{-
flip-nontriv : flip ≢ id
flip-nontriv p = {!i ⊢ j ⊢ transport (p i) (loop j)  !}
  where
    q : inv loop ≡ loop
    q = {!i ⊢ cong (λ f → f (loop i)) (cong transport p)!}
-}

_■_ : S¹ → S¹ → S¹
base ■ base = base
base ■ loop j = loop j
loop i ■ base = loop i
loop i ■ loop j =
  hcomp (λ h → λ { (i = i0) → loop j
                 ; (i = i1) → loop (h ∧ j)
                 ; (j = i0) → loop i
                 ; (j = i1) → loop (h ∧ i) }) (loop (i ∨ j))

■-comm : ∀ x y → x ■ y ≡ y ■ x
■-comm base base = id
■-comm base (loop j) = id
■-comm (loop i) base = id
■-comm (loop i) (loop j) = id

_■′_ : base ≡ base → base ≡ base → base ≡ base
(p ■′ q) i = p i ■ q i

instance
  show-S¹ : Show S¹
  Show.show show-S¹ base = "base"
  Show.show show-S¹ (loop _) = "base"

  show-path-base : Show (base ≡ base)
  Show.show show-path-base p = "loop^" ⋯ show (encode p)
