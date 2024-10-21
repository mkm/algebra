{-# OPTIONS --cubical --erasure --guardedness #-}
module Data.Bool where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Path.Equiv.Univalence
open import Data.Decision
open import Data.Truncation
open import Data.Show

bool-rec : ∀ {ℓ} {A : Type ℓ} → A → A → Bool → A
bool-rec x _ false = x
bool-rec _ y true = y

false-vs-true : false ≢ true
false-vs-true p = transport (λ i → bool-rec ⊤ ⊥ (p i)) tt

not : Bool → Bool
not false = true
not true = false

_&&_ : Bool → Bool → Bool
false && _ = false
true && b = b

_||_ : Bool → Bool → Bool
false || b = b
true || _ = true

_^^_ : Bool → Bool → Bool
false ^^ b = b
true ^^ b = not b

&&-true : ∀ b → b && true ≡ b
&&-true false = refl
&&-true true = refl

&&-assoc : ∀ a b c → (a && b) && c ≡ a && (b && c)
&&-assoc false b c = refl
&&-assoc true b c = refl

not-is-equiv : IsEquiv not
linv not-is-equiv = not
rinv not-is-equiv = not
is-linv not-is-equiv _ false = false
is-linv not-is-equiv _ true = true
is-rinv not-is-equiv _ false = false
is-rinv not-is-equiv _ true = true

not-equiv : Bool ≅ Bool
fun not-equiv = not
is-equiv not-equiv = not-is-equiv

not-path : Bool ≡ Bool
not-path = equiv-path not-equiv

^^-path : Bool → Bool ≡ Bool
^^-path false = refl
^^-path true = not-path

bool-pigeon : (p : Bool ≡ Bool) → transport p true ≡ not (transport p false)
bool-pigeon p with inspect (transport p false) | inspect (transport p true)
bool-pigeon p | false , q | false , r = absurd (false-vs-true $ transport-inj₂ p false true (q ■ inv r))
bool-pigeon p | false , q | true , r = r ■ λ i → not (q (~ i))
bool-pigeon p | true , q | false , r = r ■ λ i → not (q (~ i))
bool-pigeon p | true , q | true , r = absurd (false-vs-true $ transport-inj₂ p false true (q ■ inv r))

data Ω₁-Bool : Ω₁ Bool → Type₁ where
  Ω₁-refl : Ω₁-Bool refl
  Ω₁-not : Ω₁-Bool not-path

Ω₁-Bool-char : (p : Ω₁ Bool) → Ω₁-Bool p
Ω₁-Bool-char p with inspect $ transport p false
Ω₁-Bool-char p | false , q = transport (λ t → Ω₁-Bool (transport-inj₁ refl p α t)) Ω₁-refl
  where
    α : transport refl ≡ transport p
    α i false = q (~ i)
    α i true = (ap not (inv q) ■ inv (bool-pigeon p)) i
Ω₁-Bool-char p | true , q = transport (λ t → Ω₁-Bool (transport-inj₁ not-path p α t)) Ω₁-not
  where
    α : transport not-path ≡ transport p
    α i false = q (~ i)
    α i true = (ap not (inv q) ■ inv (bool-pigeon p)) i

bool-aut : Ω₁ Bool ≅ Bool
fun bool-aut p = transport p false 
linv (is-equiv bool-aut) = ^^-path
rinv (is-equiv bool-aut) = ^^-path
is-linv (is-equiv bool-aut) _ p with Ω₁-Bool-char p
is-linv (is-equiv bool-aut) _ .refl | Ω₁-refl = refl
is-linv (is-equiv bool-aut) _ .not-path | Ω₁-not = not-path
is-rinv (is-equiv bool-aut) _ false = false
is-rinv (is-equiv bool-aut) _ true = true

data EquivBool : Bool ≅ Bool → Type where
  equiv-bool-id : EquivBool ≅-id
  equiv-bool-not : EquivBool not-equiv

equiv-bool-not-comm : (α : Bool ≅ Bool) → not ∘ fun α ≡ fun α ∘ not
equiv-bool-not-comm α i false with inspect (fun α false) | inspect (fun α true)
equiv-bool-not-comm α i false | false , p | false , q = the (not (fun α false) ≡ fun α true) (absurd $ false-vs-true (equiv-inj α (p ■ inv q))) i
equiv-bool-not-comm α i false | false , p | true , q = (ap not p ■ inv q) i
equiv-bool-not-comm α i false | true , p | false , q = (ap not p ■ inv q) i
equiv-bool-not-comm α i false | true , p | true , q = the (not (fun α false) ≡ fun α true) (absurd $ false-vs-true (equiv-inj α (p ■ inv q))) i
equiv-bool-not-comm α i true = {! !}

equiv-bool-char : (α : Bool ≅ Bool) → EquivBool α
equiv-bool-char α with inspect $ fun α false
equiv-bool-char α | false , p = transport (λ t → EquivBool (q t)) equiv-bool-id
  where
    q : ≅-id ≡ α
    q = equiv-equal ≅-id α λ where
      i false → p (~ i)
      i true → (ap not (inv p) ■ (λ i → equiv-bool-not-comm α i false)) i
equiv-bool-char α | true , p = {! !}

data BoolEquivs {ℓ} {A : Type ℓ} : Bool ≅ A → Bool ≅ A → Type ℓ where
  bool-equivs-eq : ∀ α → BoolEquivs α α
  bool-equivs-flip : ∀ α → BoolEquivs (not-equiv ≅-∘ α) α

bool-equivs : ∀ {ℓ} {A : Type ℓ} (α β : Bool ≅ A) → BoolEquivs α β
bool-equivs α β with inspect (α ≅-∘ ≅-inv β)
bool-equivs α β | γ , p with equiv-bool-char γ
bool-equivs α β | .≅-id , p | equiv-bool-id = transport (λ t → BoolEquivs α (αβ t)) (bool-equivs-eq α)
  where
    αβ : α ≡ β
    αβ = equiv-equal α β λ where
      i false → {! !}
      i true → {! !}
bool-equivs α β | .not-equiv , p | equiv-bool-not = {! !}
  where
    αβ : α ≡ not-equiv ≅-∘ β
    αβ = {! !}

ind-bool-aut : ∀ {ℓ} (A : Bool ≡ Bool → Type ℓ) → A refl → A not-path → (p : Bool ≡ Bool) → A p
ind-bool-aut A x y p with inspect (fun bool-aut p)
ind-bool-aut A x y p | false , q = transport (λ t → A (α t)) x 
  where
    α : refl ≡ p
    α = (λ i → ^^-path (q (~ i))) ■ (λ i → is-linv (is-equiv bool-aut) i p)
ind-bool-aut A x y p | true , q = transport (λ t → A (α t)) y
  where
    α : not-path ≡ p
    α = (λ i → ^^-path (q (~ i))) ■ (λ i → is-linv (is-equiv bool-aut) i p)

bool-set : IsSet Bool
bool-set false false p q i j = along (p j) (q j) (between i0 j p) (between i0 j q) i
  where
    along : ∀ pⱼ qⱼ → false ≡ pⱼ → false ≡ qⱼ → pⱼ ≡ qⱼ
    along false false p₀ⱼ q₀ⱼ = refl
    {-# CATCHALL #-}
    along pⱼ qⱼ p₀ⱼ q₀ⱼ = inv p₀ⱼ ■ q₀ⱼ
bool-set false true p = absurd $ false-vs-true p
bool-set true false p = absurd $ false-vs-true (inv p)
bool-set true true p q i j = along (p j) (q j) (between i0 j p) (between i0 j q) i
  where
    along : ∀ pⱼ qⱼ → true ≡ pⱼ → true ≡ qⱼ → pⱼ ≡ qⱼ
    along true true p₀ⱼ q₀ⱼ = refl
    {-# CATCHALL #-}
    along pⱼ qⱼ p₀ⱼ q₀ⱼ = inv p₀ⱼ ■ q₀ⱼ

data So : Bool → Type where
  oh : So true

uh-oh : So false → ⊥
uh-oh ()

dec-so : ∀ b → Dec (So b)
dec-so false = no λ ()
dec-so true = yes oh

so-prop : ∀ {b} → IsProp (So b)
so-prop = lemma refl
  where
    lemma : ∀ {b₁ b₂} (p : b₁ ≡ b₂) (x : So b₁) (y : So b₂) → Path (λ i → So (p i)) x y
    lemma p oh oh = transport (λ i → Path (λ j → So (bool-set true true refl p i j)) oh oh) refl

instance
  bool-show : Show Bool
  show ⦃ bool-show ⦄ = bool-rec "false" "true"
  next ⦃ bool-show ⦄ = show-refl

{-
  bool-coshow : Coshow Bool
  coshow ⦃ bool-coshow ⦄ f = "λ { false → " ++ show (f false) ++ " ; true → " ++ show (f true) ++ " }"
-}
