{-# OPTIONS --cubical --prop #-}
module Show where

open import Path
open import String

record Show (A : Type) : Type where
  field
    show : A → String

open Show ⦃ … ⦄ public

instance
  show-String : Show String
  Show.show show-String x = x

ShowPath : Type → Type
ShowPath A = {x y : A} → Show (x ≡ y)

{-
record ShowPath (A : Type) : Type where
  field
    show-path : ∀ {x y : A} → x ≡ y → String

instance
  show-path : ∀ {A} → ⦃ _ : ShowPath A ⦄ {x y : A} → Show (x ≡ y)
  Show.show (show-path {_} ⦃ s ⦄) = ShowPath.show-path s
-}
