{-# OPTIONS --cubical --erasure --guardedness #-}
module Algebra.Monoid.Free where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Data.Truncation
open import Data.Bool
open import Data.Nat hiding (_·_)
open import Data.List using (List; []; _∷_; _++_; ++-[]; list-set)
open import Data.Sigma
open import Data.Decision
import Algebra.Monoid as M

private
  variable
    ℓ : Level
    A : Type ℓ

data Free {ℓ} (A : Type ℓ) : Type ℓ
data _∼_ {A : Type ℓ} : Free A → Free A → Type ℓ

infix 4 _∼_

data Free A where
  ⟨_⟩ : A → Free A
  ε : Free A
  _·_ : Free A → Free A → Free A
  sim : ∀ {x y} → x ∼ y → x ≡ y
  free-set : IsSet (Free A)

infixr 40 _·_

data _∼_ where
  ε-left : ∀ x → ε · x ∼ x
  ε-right : ∀ x → x · ε ∼ x
  ·-assoc : ∀ x y z → (x · y) · z ∼ x · (y · z)

ε-both : ε · ε ∼ ε
ε-both = ε-left ε

free-rec : ∀ {ℓ′} {B : Type ℓ′} (s : A → B) (e : B) (m : B → B → B)
  → (∀ x → m e x ≡ x) → (∀ x → m x e ≡ x) → (∀ x y z → m (m x y) z ≡ m x (m y z)) → IsSet B
  → (x : Free A) → B
free-rec s e m e-left e-right m-assoc B-set ⟨ a ⟩ = s a
free-rec s e m e-left e-right m-assoc B-set ε = e
free-rec s e m e-left e-right m-assoc B-set (x · y) =
  m (free-rec s e m e-left e-right m-assoc B-set x) (free-rec s e m e-left e-right m-assoc B-set y)
free-rec s e m e-left e-right m-assoc B-set (sim (ε-left x) i) =
  e-left (free-rec s e m e-left e-right m-assoc B-set x) i
free-rec s e m e-left e-right m-assoc B-set (sim (ε-right x) i) =
  e-right (free-rec s e m e-left e-right m-assoc B-set x) i
free-rec s e m e-left e-right m-assoc B-set (sim (·-assoc x y z) i) =
  m-assoc
    (free-rec s e m e-left e-right m-assoc B-set x)
    (free-rec s e m e-left e-right m-assoc B-set y)
    (free-rec s e m e-left e-right m-assoc B-set z)
    i
free-rec s e m e-left e-right m-assoc B-set (free-set x y p q i j) =
  B-set _ _
    (λ j → free-rec s e m e-left e-right m-assoc B-set (p j))
    (λ j → free-rec s e m e-left e-right m-assoc B-set (q j)) i j

free-ind-prop : ∀ {ℓ′} {B : Free A → Type ℓ′} → ((x : Free A) → IsProp (B x))
  → ((x : A) → B ⟨ x ⟩) → B ε → (∀ {x y} → B x → B y → B (x · y)) → (x : Free A) → B x
free-ind-prop B-prop s e m ⟨ x ⟩ = s x
free-ind-prop B-prop s e m ε = e
free-ind-prop B-prop s e m (x · y) = m (free-ind-prop B-prop s e m x) (free-ind-prop B-prop s e m y)
free-ind-prop B-prop s e m (sim (ε-left x) i) =
  prop-fill
    (λ i → B-prop (sim (ε-left x) i)) i
    λ where
      i (i = i0) → m e (free-ind-prop B-prop s e m x)
      i (i = i1) → free-ind-prop B-prop s e m x
free-ind-prop B-prop s e m (sim (ε-right x) i) =
  prop-fill
    (λ i → B-prop (sim (ε-right x) i)) i
    λ where
      i (i = i0) → m (free-ind-prop B-prop s e m x) e
      i (i = i1) → free-ind-prop B-prop s e m x
free-ind-prop B-prop s e m (sim (·-assoc x y z) i) =
  prop-fill
    (λ i → B-prop (sim (·-assoc x y z) i)) i
    λ where
      i (i = i0) → m (m (free-ind-prop B-prop s e m x) (free-ind-prop B-prop s e m y)) (free-ind-prop B-prop s e m z)
      i (i = i1) → m (free-ind-prop B-prop s e m x) (m (free-ind-prop B-prop s e m y) (free-ind-prop B-prop s e m z))
free-ind-prop B-prop s e m (free-set x y p q i j) =
  set-fill (λ i j → prop-to-set (B-prop (free-set x y p q i j))) i j
    λ where
      i j (j = i0) → free-ind-prop B-prop s e m x
      i j (i = i0) → free-ind-prop B-prop s e m (p j)
      i j (i = i1) → free-ind-prop B-prop s e m (q j)
      i j (j = i1) → free-ind-prop B-prop s e m y

size : Free A → ℕ
size ⟨ _ ⟩ = 1
size ε = 0
size (x · y) = size x + size y
size (sim (ε-left x) i) = size x
size (sim (ε-right x) i) = +-zero (size x) i
size (sim (·-assoc x y z) i) = (size x +₃ size y +₃ size z) i
size (free-set x y p q i j) = ℕ-set _ _ (λ j → size (p j)) (λ j → size (q j)) i j

ε-vs-⟨_⟩ : (a : A) → ε ≢ ⟨ a ⟩
ε-vs-⟨ a ⟩ p = false-vs-true λ i → size (p i) ≟ 1

{-
dec-≡ : (x y : Free A) → Dec (x ≡ y)
dec-≡ x y = {! !}
-}

ε-vs-· : (x y : Free A) → ε ≡ x · y → (ε ≡ x) × (ε ≡ y)
ε-vs-· =
  free-ind-prop
    (λ _ → pi-prop λ _ → fun-prop (×-prop (free-set _ _) (free-set _ _)))
    (λ a x p → absurd $ zero-vs-succ λ i → size (p i))
    (λ x p → refl , p ■ sim (ε-left x))
    λ {x = x} {y = y} hx hy z p →
      let q , r = hx (y · z) (p ■ sim (·-assoc x y z))
          s , t = hy z r
      in inv (sim ε-both) ■ (λ i → q i · s i) , t
{-
ε-vs-· ⟨ _ ⟩ _ p = absurd $ zero-vs-succ λ i → size (p i)
ε-vs-· ε x p = refl , p ■ ε-left x
ε-vs-· (x · y) z p =
  let q , r = ε-vs-· x (y · z) (p ■ ·-assoc x y z)
      s , t = ε-vs-· y z r
  in inv ε-both ■ (λ i → q i · s i) , t
ε-vs-· (ε-left x i) y p = {! !}
ε-vs-· x y p = {! !}
-}

dec-ε : (x : Free A) → Dec (x ≡ ε)
dec-ε =
  free-ind-prop
    (λ x → dec-prop (free-set x ε))
    (λ a → no λ p → ε-vs-⟨ a ⟩ (inv p))
    (yes refl)
    λ where
      (yes p) (yes q) → yes ((λ i → p i · q i) ■ sim ε-both)
      {x = x} {y = y} (yes p) (no q) → no λ r → q $ inv (sim (ε-left y)) ■ (λ i → p (~ i) · y) ■ r
      {x = x} {y = y} (no p) (yes q) → no λ r → p $ inv (sim (ε-right x)) ■ (λ i → x · q (~ i)) ■ r
      {x = x} {y = y} (no p) (no q) → no λ r → p (inv (fst (ε-vs-· x y (inv r))))

reverse : Free A → Free A
reverse ⟨ a ⟩ = ⟨ a ⟩
reverse ε = ε
reverse (x · y) = reverse y · reverse x
reverse (sim (ε-left x) i) = sim (ε-right (reverse x)) i
reverse (sim (ε-right x) i) = sim (ε-left (reverse x)) i
reverse (sim (·-assoc x y z) i) = sim (·-assoc (reverse z) (reverse y) (reverse x)) (~ i)
reverse (free-set x y p q i j) = free-set _ _ (λ j → reverse (p j)) (λ j → reverse (q j)) i j

reverse-reverse : (x : Free A) → reverse (reverse x) ≡ x
reverse-reverse ⟨ _ ⟩ = refl
reverse-reverse ε = refl
reverse-reverse (x · y) i = reverse-reverse x i · reverse-reverse y i
reverse-reverse (sim {x} {y} s i) j =
  set-fill (λ _ _ → free-set) i j
    λ where
      i j (j = i0) → reverse (reverse (sim s i))
      i j (i = i0) → reverse-reverse x j
      i j (i = i1) → reverse-reverse y j
      i j (j = i1) → sim s i
reverse-reverse (free-set x y p q i j) =
  set-fill (λ i j → prop-to-set (free-set (reverse (reverse (free-set x y p q i j))) (free-set x y p q i j))) i j
    λ where
      i j (j = i0) → reverse-reverse x
      i j (i = i0) → reverse-reverse (p j)
      i j (i = i1) → reverse-reverse (q j)
      i j (j = i1) → reverse-reverse y

join : Free (Free A) → Free A
join ⟨ x ⟩ = x
join ε = ε
join (x · y) = join x · join y
join (sim (ε-left x) i) = sim (ε-left (join x)) i
join (sim (ε-right x) i) = sim (ε-right (join x)) i
join (sim (·-assoc x y z) i) = sim (·-assoc (join x) (join y) (join z)) i
join (free-set x y p q i j) = free-set _ _ (λ j → join (p j)) (λ j → join (q j)) i j

map : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → (A → B) → Free A → Free B
map f ⟨ a ⟩ = ⟨ f a ⟩
map f ε = ε
map f (x · y) = map f x · map f y
map f (sim (ε-left x) i) = sim (ε-left (map f x)) i
map f (sim (ε-right x) i) = sim (ε-right (map f x)) i
map f (sim (·-assoc x y z) i) = sim (·-assoc (map f x) (map f y) (map f z)) i
map f (free-set x y p q i j) = free-set _ _ (λ j → map f (p j)) (λ j → map f (q j)) i j

map-size : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} (f : A → B) (x : Free A) → size (map f x) ≡ size x
map-size f = free-ind-prop (λ _ → ℕ-set _ _) (λ _ → refl) refl λ p q i → p i + q i

_·′_ : Free A → Free A → Free A
x ·′ y = free-rec (λ a x → x · ⟨ a ⟩) (λ x → x) (λ f g x → g (f x)) (λ _ → refl) (λ _ → refl) (λ _ _ _ → refl) (fun-set free-set) y x

·′-same : (x y : Free A) → x ·′ y ≡ x · y
·′-same x y =
  free-ind-prop
    {B = λ y → ∀ x → x ·′ y ≡ x · y}
    (λ _ → pi-prop λ _ → free-set _ _)
    (λ _ _ → refl)
    (λ x i → sim (ε-right x) (~ i))
    (λ {x = y} {y = z} p q x → (λ i → q (p x i) i) ■ sim (·-assoc x y z))
    y x

ε-left′ : (x : Free A) → ε ·′ x ≡ x
ε-left′ x = transport (λ t → ·′-same ε x (~ t) ≡ x) (sim (ε-left x))

foldr : ∀ {ℓ′} {B : Type ℓ′} → IsSet B → B → (A → B → B) → Free A → B
foldr B-set k f ⟨ a ⟩ = f a k
foldr B-set k f ε = k
foldr B-set k f (x · y) = foldr B-set (foldr B-set k f y) f x
foldr B-set k f (sim (ε-left x) _) = foldr B-set k f x
foldr B-set k f (sim (ε-right x) _) = foldr B-set k f x
foldr B-set k f (sim (·-assoc x y z) _) = foldr B-set (foldr B-set (foldr B-set k f z) f y) f x
foldr B-set k f (free-set x y p q i j) = B-set _ _ (λ j → foldr B-set k f (p j)) (λ j → foldr B-set k f (q j)) i j

_·ᶜ_ : Free A → Free A → Free A
x ·ᶜ y = choose (dec-ε x) y (choose (dec-ε y) x (x · y))

infixr 40 _·ᶜ_

·ᶜ-is-· : (x y : Free A) → x ·ᶜ y ≡ x · y
·ᶜ-is-· x y with dec-ε x | dec-ε y
·ᶜ-is-· x y | yes p | _ = inv (sim (ε-left y)) ■ (λ i → p (~ i) · y)
·ᶜ-is-· x y | no _ | yes q = inv (sim (ε-right x)) ■ (λ i → x · q (~ i))
·ᶜ-is-· x y | no p | no q = refl

prune′ : (x : Free A) → BasedPath x
prune′ = free-ind-prop based-path-prop (λ a → ⟨ a ⟩ , refl) (ε , refl) λ (x , p) (y , q) → (x ·ᶜ y) , (λ i → p i · q i) ■ inv (·ᶜ-is-· x y)

prune : Free A → Free A
prune = fst ∘ prune′

safe-tail′ : Free A → Free A → Free A → Free A
safe-tail′ d z ⟨ _ ⟩ = z
safe-tail′ d z ε = d
safe-tail′ d z (x · y) = safe-tail′ (safe-tail′ d z y) (y ·′ z) x
safe-tail′ d z (sim (ε-left x) _) = safe-tail′ d z x
safe-tail′ d z (sim (ε-right x) i) = safe-tail′ d (ε-left′ z i) x
safe-tail′ d z (sim (·-assoc x y w) i) = safe-tail′ (safe-tail′ (safe-tail′ d z w) (w ·′ z) y) (p i) x
  where
    p : y ·′ (w ·′ z) ≡ (y · w) ·′ z
    p = (λ i → y ·′ ·′-same w z i) ■ λ i → ·′-same y w i ·′ z
safe-tail′ d z (free-set x y p q i j) = free-set _ _ (λ j → safe-tail′ d z (p j)) (λ j → safe-tail′ d z (q j)) i j

safe-tail : Free A → Free A
safe-tail = safe-tail′ ε ε

module _ {A : Type ℓ} (A-set : IsSet A) where

  safe-head : A → Free A → A
  safe-head d = foldr A-set d const

  data Uncons : Free A → Type ℓ where
    empty : Uncons ε
    split : (a : A) (x : Free A) → Uncons (⟨ a ⟩ · x)

  uncons-prop′ : {x y : Free A} (p : x ≡ y) (u₁ : Uncons x) (u₂ : Uncons y) → Path (λ i → Uncons (p i)) u₁ u₂
  uncons-prop′ p empty empty = transport (λ t → Path (λ i → Uncons (free-set _ _ refl p t i)) empty empty) refl
  uncons-prop′ p empty (split b y) = absurd $ zero-vs-succ λ i → size (p i)
  uncons-prop′ p (split a x) empty = absurd $ zero-vs-succ λ i → size (p (~ i))
  uncons-prop′ p (split a x) (split b y) =
    transport
      (λ t → Path (λ i → Uncons (free-set _ _ p′ p t i)) (split a x) (split b y))
      λ i → split (safe-head a (p i)) (safe-tail (p i))
    where
      p′ : ⟨ a ⟩ · x ≡ ⟨ b ⟩ · y
      p′ i = ⟨ safe-head a (p i) ⟩ · safe-tail (p i)

  uncons-prop : (x : Free A) → IsProp (Uncons x)
  uncons-prop x = uncons-prop′ (λ _ → x)

  uncons : (x : Free A) → Uncons x
  uncons =
    free-ind-prop
      uncons-prop
      (λ a → transport (λ t → Uncons (sim (ε-right ⟨ a ⟩) t)) (split a ε))
      empty
      λ where
        {y = y} empty u → transport (λ t → Uncons (sim (ε-left y) (~ t))) u
        {y = y} (split a x) u → transport (λ t → Uncons (sim (·-assoc ⟨ a ⟩ x y) (~ t))) (split a (x · y))

  ⟨⟩-inj : {a b : A} → ⟨ a ⟩ ≡ ⟨ b ⟩ → a ≡ b
  ⟨⟩-inj {a = a} p i = safe-head a (p i)

  prepend-list : Free A → List A → List A
  prepend-list x xs = foldr (list-set A-set) xs _∷_ x

  to-list : Free A → List A
  to-list x = prepend-list x []

  from-list : List A → Free A
  from-list [] = ε
  from-list (x ∷ xs) = ⟨ x ⟩ · from-list xs

  prepend-from-list : (xs ys : List A) → prepend-list (from-list xs) ys ≡ xs ++ ys
  prepend-from-list [] ys _ = ys
  prepend-from-list (x ∷ xs) ys i = x ∷ prepend-from-list xs ys i

  to-from-list : (xs : List A) → to-list (from-list xs) ≡ xs
  to-from-list xs = prepend-from-list xs [] ■ ++-[] xs

  from-prepend-list : (x : Free A) (xs : List A) → from-list (prepend-list x xs) ≡ x · from-list xs
  from-prepend-list =
    free-ind-prop
      (λ _ → pi-prop λ _ → free-set _ _)
      (λ x xs → refl)
      (λ xs i → sim (ε-left (from-list xs)) (~ i))
      λ {x = x} {y = y} p q xs → p (prepend-list y xs) ■ (λ i → x · q xs i) ■ inv (sim (·-assoc x y (from-list xs)))

  from-to-list : (x : Free A) → from-list (to-list x) ≡ x
  from-to-list x = from-prepend-list x [] ■ sim (ε-right x)

  free-list-equiv : Free A ≅ List A
  fun free-list-equiv = to-list
  linv (is-equiv free-list-equiv) = from-list
  rinv (is-equiv free-list-equiv) = from-list
  is-linv (is-equiv free-list-equiv) i x = from-to-list x i
  is-rinv (is-equiv free-list-equiv) i x = to-from-list x i

  free-list-eq : Free A ≡ List A
  free-list-eq = equiv-path free-list-equiv

  ε-[]-eq : Path (λ i → free-list-eq i) ε []
  ε-[]-eq = pathₚ _ λ _ → []

·-inj₁ : (x x′ y : Free A) → x · y ≡ x′ · y → x ≡ x′
·-inj₁ ⟨ a ⟩ ⟨ b ⟩ y p i = safe-head free-set ε (map ⟨_⟩ (p i))
·-inj₁ ⟨ a ⟩ ε y p = absurd $ nat-vs-succ (inv (ap size p))
·-inj₁ ⟨ a ⟩ (x₁′ · x₂′) y p = {! !}
·-inj₁ ε x′ y p = {! !}
·-inj₁ (x₁ · x₂) x′ y p = {! !}
·-inj₁ x x′ y p = {! !}

{-
  data Head (d : A) : Free A → A → Type ℓ where
    head-default : Head d ε d
    head-here : ∀ a → Head d ⟨ a ⟩ a
    head-fst : ∀ x y a → x ≢ ε → Head d x a → Head d (x · y) a

  head-prop′ : ∀ {x x′ : Free A} {d a a′ : A} → (p : x ≡ x′) (q : a ≡ a′) (h₁ : Head d x a) (h₂ : Head d x′ a′) → Path (λ i → Head d (p i) (q i)) h₁ h₂

  head-prop : ∀ {x : Free A} {d a : A} → IsProp (Head d x a)
  head-prop = head-prop′ refl refl

  head′ : (d : A) (x : Free A) → Σ A λ a → Head d x a
  head′ d = free-ind-prop {! !} (λ a → a , head-here a) (d , head-default) {! !}

  head : A → (x : Free A) → A
  head d x = fst $ head′ d x

  head-prop′ p q (head-here a) (head-here a′) i = {! free-set _ _ p (ap ⟨_⟩ (ap (head a) p)) !}
  head-prop′ p q (head-here a) (head-fst x y a′ np h₂) = {! !}
  head-prop′ p q h₁ h₂ = {! !}
-}

{-
data Elem where
  ⟨_⟩ₑ : ∀ x → Elem ⟨ x ⟩
  εₑ : Elem ε
  _·ₑ_ : ∀ {x y} → Elem x → Elem y → Elem (x · y)

elem-prop′ : ∀ {ℓ} {A : Type ℓ} {x y : Free A} (p : x ≡ y) (ex : Elem x) (ey : Elem y) → Path (λ i → Elem (p i)) ex ey
elem-prop′ p ⟨ x ⟩ₑ ey = {!!}
elem-prop′ p εₑ ⟨ x ⟩ₑ = {!!}
elem-prop′ p εₑ εₑ i = {!transp (λ j → Elem (p (i ∧ j))) (i ≈ i0) εₑ!}
elem-prop′ p εₑ (ey ·ₑ ey₁) = {!!}
elem-prop′ p (ex ·ₑ ex₁) ey = {!!}

elem-prop : ∀ {ℓ} {A : Type ℓ} {x : Free A} → IsProp (Elem x)
elem-prop e e′ = elem-prop′ refl e e′

test-ε : ∀ {ℓ} {A : Type ℓ} (x : Free A) → Bool
test-ε ⟨ _ ⟩ = false
test-ε ε = true
test-ε (x · y) = test-ε x && test-ε y
test-ε (ε-left x i) = test-ε x
test-ε (ε-right x i) = &&-true (test-ε x) i
test-ε (·-assoc x y z i) = &&-assoc (test-ε x) (test-ε y) (test-ε z) i

⟨⟩-vs-ε : ∀ {ℓ} {A : Type ℓ} (x : A) → ⟨ x ⟩ ≢ ε
⟨⟩-vs-ε {A = A} x p = uh-oh $ transport (λ i → So $ not (test-ε (p i))) oh

is-ε : ∀ {ℓ} {A : Type ℓ} (x : Free A) → Dec (x ≡ ε)
is-ε ⟨ _ ⟩ = no $ ⟨⟩-vs-ε _
is-ε ε = yes refl
is-ε (x · y) with is-ε x | is-ε y
is-ε (x · y) | yes α | yes β  = yes $ (λ i → α i · β i) ■ ε-left ε
is-ε (x · y) | yes α | no β = no λ p → β (inv (ε-left y) ■₃ (λ i → α (~ i) · y) ■₃ p)
is-ε (x · y) | no α | _ = no λ p → α {!!}
is-ε (ε-left x i) with is-ε x
is-ε (ε-left x i) | yes α = {!!}
is-ε (ε-left x i) | no α = {!!}
is-ε (ε-right x i) with is-ε x
is-ε (ε-right x i) | yes α = {!!}
is-ε (ε-right x i) | no α = {!!}
is-ε (·-assoc x y z i) with is-ε x | is-ε y | is-ε z
is-ε (·-assoc x y z i) | yes α | yes β | yes γ = {!!}
is-ε (·-assoc x y z i) | yes α | yes β | no γ = {!!}
is-ε (·-assoc x y z i) | yes α | no β | γ = {!!}
is-ε (·-assoc x y z i) | no α | β | γ = {!!}

from-⟨⟩ : ∀ {ℓ} {A : Type ℓ} → A → Free A → A
from-⟨⟩ a ⟨ b ⟩ = b
from-⟨⟩ a ε = a
from-⟨⟩ a (x · y) = from-⟨⟩ (from-⟨⟩ a y) x
from-⟨⟩ a (ε-left x _) = from-⟨⟩ a x
from-⟨⟩ a (ε-right x _) = from-⟨⟩ a x
from-⟨⟩ a (·-assoc x y z _) = from-⟨⟩ (from-⟨⟩ (from-⟨⟩ a z) y) x

from-·₁ : ∀ {ℓ} {A : Type ℓ} {x : Free A} → Free A → Elem x → Free A
from-·₁ y ⟨ _ ⟩ₑ = y
from-·₁ y εₑ = y
from-·₁ {x = ._·_ x _} _ (_ ·ₑ _) = x

from-·₂ : ∀ {ℓ} {A : Type ℓ} {x : Free A} → Free A → Elem x → Free A
from-·₂ y ⟨ _ ⟩ₑ = y
from-·₂ y εₑ = y
from-·₂ {x = ._·_ _ x} _ (_ ·ₑ _) = x

essence : ∀ {ℓ} {A : Type ℓ} {x : Free A} → Elem x → x ≡ x → x ≡ x
·-essence : ∀ {ℓ} {A : Type ℓ} {x y : Free A} → Elem x → Elem y → x · y ≡ x · y → x · y ≡ x · y

essence ⟨ a ⟩ₑ p i = ⟨ from-⟨⟩ a (p i) ⟩
essence εₑ _ _ = ε
essence (e₁ ·ₑ e₂) = ·-essence e₁ e₂

·-essence ⟨ x ⟩ₑ ey p i = {!!}
·-essence εₑ ey p = {!!} -- ε-left _ ■₃ essence ey (inv (ε-left _) ■₃ p ■₃ ε-left _) ■₃ inv (ε-left _)
·-essence (ex₁ ·ₑ ex₂) ey p = {!·-essence !} -- ·-assoc _ _ _ ■₃ ·-essence ex₁ (ex₂ ·ₑ ey) (inv (·-assoc _ _ _) ■₃ p ■₃ ·-assoc _ _ _) ■₃ inv (·-assoc _ _ _)

{-
essence : ∀ {ℓ} {A : Type ℓ} {x y : Free A} → Elem x → Elem y → x ≡ y → x ≡ y
essence {A = A} ⟨ x ⟩ₑ ⟨ y ⟩ₑ p j = along (p j) (between i0 j p)
  where
    along : ∀ pⱼ → ⟨ x ⟩ ≡ pⱼ → Free A
    along ⟨ pⱼ ⟩ p₀ⱼ = ⟨ pⱼ ⟩
    along ε p₀ⱼ = ε
    along (pⱼ · qⱼ) p₀ⱼ with is-ε pⱼ
    along (pⱼ · qⱼ) p₀ⱼ | yes α = pⱼ
    along (pⱼ · qⱼ) p₀ⱼ | no α = along qⱼ {!!}
    along (ε-left pⱼ i) p₀ⱼ = {!!}
    along (ε-right pⱼ i) p₀ⱼ = {!!}
    along (·-assoc pⱼ pⱼ₁ pⱼ₂ i) p₀ⱼ = {!!}
essence {A = A} ⟨ x ⟩ₑ εₑ p = {!!}
essence {A = A} ⟨ x ⟩ₑ (ey₁ ·ₑ ey₂) p = {!!}
essence {A = A} εₑ ⟨ x ⟩ₑ p = {!!}
essence {A = A} εₑ εₑ p _ = ε
essence {A = A} εₑ (ey₁ ·ₑ ey₂) p = {!!}
essence {A = A} (ex₁ ·ₑ ex₂) ey p = {!!}
-}

roundabout : ⟨ base ⟩ ≡ ⟨ base ⟩
roundabout = inv (ε-left ⟨ base ⟩) ■₃ (inv (ε-right (ε · ⟨ base ⟩)) ■₃ ·-assoc ε ⟨ base ⟩ ε ■₃ ε-left (⟨ base ⟩ · ε)) ■₃ ε-right ⟨ base ⟩
-}
