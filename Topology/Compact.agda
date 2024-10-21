{-# OPTIONS --cubical --erasure --guardedness #-}
module Topology.Compact where

open import Prelude
open import Path.Comp
open import Data.Bool

record Compact {ℓ} (A : Type ℓ) : Type ℓ where
  field
    witness : (f : A → Bool) → A
    universal : (f : A → Bool) (x : A) → So (f x) → So (f (witness f))

open Compact public

bool-compact : Compact Bool
witness bool-compact f = f true
universal bool-compact f false _ with inspect $ f true
universal bool-compact f false α | false , p = transport (λ i → So (f (p (~ i)))) α
universal bool-compact f false _ | true , p = transport (λ i → So ((ap f p ■ p) (~ i))) oh 
universal bool-compact f true _ with inspect $ f true
universal bool-compact f true α | false , p with inspect $ f false
universal bool-compact f true α | false , p | false , q = absurd $ uh-oh (transport (λ i → So (p i)) α)
universal bool-compact f true α | false , p | true , q = transport (λ i → So ((ap f p ■ q) (~ i))) oh
universal bool-compact f true _ | true , p = transport (λ i → So ((ap f p ■ p) (~ i))) oh
