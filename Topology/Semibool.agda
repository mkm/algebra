{-# OPTIONS --cubical --guardedness #-}
module Topology.Semibool where

open import Prelude
open import Path.Comp hiding (repeat)
open import Data.Truncation
open import Data.Stream

data 𝔹 : Type where
  any : Stream Bool → 𝔹
  false-head : ∀ {bs} → head bs ≡ false → any bs ≡ any (tail bs)
  true-head : ∀ {bs} → head bs ≡ true → any bs ≡ any (repeat true)

sfalse : 𝔹
sfalse = any $ repeat false

strue : 𝔹
strue = any $ repeat true

𝔹-set : IsSet 𝔹
𝔹-set (any bs) (any bs′) p q i j = along (p j) (q j) (between i0 j p) (between i0 j q) {!λ i → !} i
  where
    from-any : 𝔹 → Stream Bool
    from-any (any bs) = bs
    from-any (false-head α i) = {!!}
    from-any (true-head α i) = {!!}
    along : (pⱼ qⱼ : 𝔹) → any bs ≡ pⱼ → any bs ≡ qⱼ → from-any pⱼ ≡ from-any qⱼ → pⱼ ≡ qⱼ
    along (any pⱼ) (any qⱼ) p₀ⱼ q₀ⱼ γ = {!!}
    along (any x) (false-head x₁ i) p₀ⱼ q₀ⱼ γ = {!!}
    along (any x) (true-head x₁ i) p₀ⱼ q₀ⱼ γ = {!!}
    along (false-head x i) qⱼ p₀ⱼ q₀ⱼ γ = {!!}
    along (true-head x i) qⱼ p₀ⱼ q₀ⱼ γ = {!!}
𝔹-set (any bs) (false-head α j) = {!!}
𝔹-set (any bs) (true-head α j) = {!!}
𝔹-set (false-head α i) y = {!!}
𝔹-set (true-head α i) y = {!!}
