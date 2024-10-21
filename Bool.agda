{-# OPTIONS --cubical --prop #-}

open import Cubical.Foundations.Isomorphism
open import Path
open import Logic

data Bool : Type where
  false : Bool
  true : Bool

false≢true : false ≢ true
false≢true p = proof (transport (λ i → T (p i)) (lift top))
  where
     T : Bool → Type
     T false = ♯ ⊤
     T true = ♯ ⊥

not : Bool → Bool
not false = true
not true = false

not-iso : Iso Bool Bool
Iso.fun not-iso = not
Iso.inv not-iso = not
Iso.rightInv not-iso false = id
Iso.rightInv not-iso true = id
Iso.leftInv not-iso false = id
Iso.leftInv not-iso true = id

not-path : Bool ≡ Bool
not-path = iso-path not-iso

bool-automorphisms : Iso Bool (Bool ≡ Bool)
Iso.fun bool-automorphisms false = id
Iso.fun bool-automorphisms true = not-path
Iso.inv bool-automorphisms p = transport p false
Iso.rightInv bool-automorphisms p = lemma (transport p false) (transport p true) id id
  where
    lemma : (x y : Bool) → x ≡ transport p false → y ≡ transport p true → Iso.fun bool-automorphisms x ≡ p
    lemma false false q r = ⊥-elim (false≢true (transport-embed p false true (q ~∘ r))) 
    lemma false true q r = transport-inj id p λ { i false → (transport-id false ∘ q) i ; i true → (transport-id true ∘ r) i }
    lemma true false q r = transport-inj not-path p λ { i false → (cong (λ f → f false) (transport-iso not-iso) ∘ q) i ; i true → (cong (λ f → f true) (transport-iso not-iso) ∘ r) i }
    lemma true true q r = ⊥-elim (false≢true (transport-embed p false true (q ~∘ r)))
Iso.leftInv bool-automorphisms false = transport-id false
Iso.leftInv bool-automorphisms true i = transport-iso not-iso i false
