{-# OPTIONS --cubical #-}
module Prim where

open import Prim.Core public
open import Prim.Interval public
open import Prim.Equiv public
open import Prim.Glue renaming (primGlue to Glue; prim^glue to glue; prim^unglue to unglue) public
