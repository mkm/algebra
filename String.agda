{-# OPTIONS --cubical --prop #-}
module String where

open import Path

postulate
  String : Type

{-# BUILTIN STRING String #-}

private
  primitive
    primStringAppend : String → String → String

_⋯_ : String → String → String
_⋯_ = primStringAppend

infixr 40 _⋯_
