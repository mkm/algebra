{-# OPTIONS --cubical #-}
module Path.Inductive where

open import Prelude

infix 4 _＝_
data _＝_ {ℓ} {A : Type ℓ} (x : A) : A → Type ℓ where
  unify : x ＝ x
