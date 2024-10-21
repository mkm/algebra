{-# OPTIONS --cubical --erasure #-}
module Data.String where

open import Prelude

private
  module Prims where
    primitive
      primStringAppend : String → String → String

    infixr 25 primStringAppend

open Prims
  renaming (primStringAppend to _++_)
  public

