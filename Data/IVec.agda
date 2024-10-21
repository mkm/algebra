{-# OPTIONS --cubical --erasure #-}
module Data.IVec where

open import Prelude
open import Data.SNat

data IVec : ℕₛ → SSet where
  [] : IVec zeroₛ
  _∷_ : ∀ {n} → I → IVec n → IVec (succₛ n)

imap : ∀ {n} → (I → I) → IVec n → IVec n
imap f [] = []
imap f (x ∷ xs) = f x ∷ imap f xs

ifoldr : ∀ {n} → I → (I → I → I) → IVec n → I
ifoldr k f [] = k
ifoldr k f (x ∷ xs) = f x (ifoldr k f xs)
