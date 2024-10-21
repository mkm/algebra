{-# OPTIONS --cubical --erasure #-}
module Reflection.Base where

open import Prelude

postulate
  Name : Type
  Meta : Type

{-# BUILTIN QNAME Name #-}
{-# BUILTIN AGDAMETA Meta #-}

primitive
  primQNameEquality : Name → Name → Bool
  primQNameLess : Name → Name → Bool
  primShowQName : Name → String

  primMetaEquality : Meta → Meta → Bool
  primMetaLess : Meta → Meta → Bool
  primShowMeta : Meta → String
  primMetaToNat : Meta → ℕ

data Lit : Type where
  nat : ℕ → Lit
  word64 : Word64 → Lit
  float : Float → Lit
  char : Char → Lit
  string : String → Lit
  name : Name → Lit
  meta : Meta → Lit

{-# BUILTIN AGDALITERAL Lit #-}
{-# BUILTIN AGDALITNAT nat #-}
{-# BUILTIN AGDALITWORD64 word64 #-}
{-# BUILTIN AGDALITFLOAT float #-}
{-# BUILTIN AGDALITCHAR char #-}
{-# BUILTIN AGDALITSTRING string #-}
{-# BUILTIN AGDALITQNAME name #-}
{-# BUILTIN AGDALITMETA meta #-}

data Visibility : Type where
  visible : Visibility
  hidden : Visibility
  inst : Visibility

{-# BUILTIN HIDING Visibility #-}
{-# BUILTIN VISIBLE visible #-}
{-# BUILTIN HIDDEN hidden #-}
{-# BUILTIN INSTANCE inst #-}

data Relevance : Type where
  relevant : Relevance
  irrelevant : Relevance

{-# BUILTIN RELEVANCE Relevance #-}
{-# BUILTIN RELEVANT relevant #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

data Quantity : Type where
  quantity-0 : Quantity
  quantity-ω : Quantity

{-# BUILTIN QUANTITY Quantity #-}
{-# BUILTIN QUANTITY-0 quantity-0 #-}
{-# BUILTIN QUANTITY-ω quantity-ω #-}
