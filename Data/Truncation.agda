{-# OPTIONS --cubical --erasure #-}
module Data.Truncation where

open import Prelude
open import Path.Comp
open import Path.Equiv
open import Path.Equiv.Univalence
open import Path.Char
open import Control.Functor
open import Control.Monad
open import Data.Truncation.Base public
open import Data.Function

private
  variable
    ℓ ℓ₁ ℓ₂ : Level

⊥-prop : IsProp ⊥
⊥-prop ()

⊤-prop : IsProp ⊤
⊤-prop _ _ = refl

recall₀ : {A : Type ℓ} → IsProp A → ∣ A ∣₀ → A
recall₀ pr (forget₀ x) = x
recall₀ pr (collapse₀ x y i) = pr (recall₀ pr x) (recall₀ pr y) i

inspect₀ : {A : Type ℓ} (x : ∣ A ∣₀) → ∣ Σ A (λ x′ → forget₀ x′ ≡ x) ∣₀
inspect₀ (forget₀ x) = forget₀ (x , refl)
inspect₀ {A = A} (collapse₀ x y i) = dprop (λ i → ∣ Σ A (λ x′ → forget₀ x′ ≡ collapse₀ x y i) ∣₀) collapse₀ (inspect₀ x) (inspect₀ y) i

absurd₀ : {A : Type ℓ} → ∣ ⊥ ∣₀ → A
absurd₀ = absurd ∘ recall₀ ⊥-prop

map-∣∣₀ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → ∣ A ∣₀ → ∣ B ∣₀
map-∣∣₀ f (forget₀ x) = forget₀ (f x)
map-∣∣₀ f (collapse₀ x y i) = collapse₀ (map-∣∣₀ f x) (map-∣∣₀ f y) i

map-id-∣∣₀ : ∀ {ℓ} (A : Type ℓ) → map-∣∣₀ {A = A} id ≡ id
map-id-∣∣₀ A i (forget₀ x) = forget₀ x
map-id-∣∣₀ A i (collapse₀ x y j) = collapse₀ (map-id-∣∣₀ A i x) (map-id-∣∣₀ A i y) j

map-∘-∣∣₀ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : B → C) (g : A → B) → map-∣∣₀ (f ∘ g) ≡ map-∣∣₀ f ∘ map-∣∣₀ g
map-∘-∣∣₀ f g i (forget₀ x) = forget₀ (f (g x))
map-∘-∣∣₀ f g i (collapse₀ x y j) = collapse₀ (map-∘-∣∣₀ f g i x) (map-∘-∣∣₀ f g i y) j

instance
  ∣∣₀-functor : Functor ∣_∣₀
  Functor.map ∣∣₀-functor = map-∣∣₀
  Functor.map-id ∣∣₀-functor = map-id-∣∣₀ _
  Functor.map-∘ ∣∣₀-functor = map-∘-∣∣₀

bind-∣∣₀ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → ∣ A ∣₀ → (A → ∣ B ∣₀) → ∣ B ∣₀
bind-∣∣₀ (forget₀ x) f = f x
bind-∣∣₀ (collapse₀ x y i) f = collapse₀ (bind-∣∣₀ x f) (bind-∣∣₀ y f) i 

bind-pure-∣∣₀ : ∀ {ℓ} {A B : Type ℓ} (x : ∣ A ∣₀) (f : A → B) → bind-∣∣₀ x (forget₀ ∘ f) ≡ map f x
bind-pure-∣∣₀ x f = collapse₀ (bind-∣∣₀ x (forget₀ ∘ f)) (map-∣∣₀ f x)

instance
  ∣∣₀-monad : Monad ∣_∣₀
  Monad.monad-functor ∣∣₀-monad = ∣∣₀-functor
  Monad.pure ∣∣₀-monad = forget₀
  Monad._>>=_ ∣∣₀-monad = bind-∣∣₀
  Monad.pure-bind ∣∣₀-monad _ _ = !
  Monad.bind-pure ∣∣₀-monad x f = collapse₀ (x >>= forget₀ ∘ f) (map f x)
  Monad.bind-assoc ∣∣₀-monad x f g = collapse₀ ((x >>= f) >>= g) (x >>= λ y → f y >>= g)

data ∣_∣₁ (A : Type ℓ) : Type ℓ where
  forget₁ : A → ∣ A ∣₁
  collapse₁ : IsSet ∣ A ∣₁

prop-equiv : {A : Type ℓ₁} {B : Type ℓ₂} → IsProp A → IsProp B → (A → B) → (B → A) → A ≅ B
fun (prop-equiv 𝒜 ℬ f g) = f
linv (is-equiv (prop-equiv 𝒜 ℬ f g)) = g
rinv (is-equiv (prop-equiv 𝒜 ℬ f g)) = g
is-linv (is-equiv (prop-equiv 𝒜 ℬ f g)) i a = 𝒜 (g (f a)) a i
is-rinv (is-equiv (prop-equiv 𝒜 ℬ f g)) i b = ℬ (f (g b)) b i

prop-path : {A B : Type ℓ} → IsProp A → IsProp B → (A → B) → (B → A) → A ≡ B
prop-path 𝒜 ℬ f g = equiv-path (prop-equiv 𝒜 ℬ f g)

prop-path-prop : {A B : Type ℓ} → IsProp A → IsProp B → IsProp (A ≡ B)
prop-path-prop 𝒜 ℬ p q = transport-inj₁ p q λ i x → ℬ (transport p x) (transport q x) i

is-prop-prop : {A : Type ℓ} → IsProp (IsProp A)
is-prop-prop 𝒜 ℬ i x y j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → 𝒜 (𝒜 x y j) (𝒜 x y j) k
    k (i = i1) → 𝒜 (𝒜 x y j) (ℬ x y j) k
    k (j = i0) → 𝒜 x x k
    k (j = i1) → 𝒜 y y k
    k (k = i0) → 𝒜 x y j

{-
prop-type-set : ∀ {ℓ} → IsSet (PropType ℓ)
prop-type-set (A , 𝒜) (B , ℬ) p q = ≡-path λ i → Σ-path (λ j → transport-inj₁ (λ i → fst (p i)) (λ i → fst (q i)) {!!} j i) {!!}
-}

fill-prop-square : {A : Type ℓ} → IsProp A → {ul ur ll lr : A} (p : ul ≡ ur) (q : ul ≡ ll) (r : ur ≡ lr) (s : ll ≡ lr)
  → ┌ p ┐
    q · r
    └ s ┘
fill-prop-square 𝒜 {ul = ul} p q r s i j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (j = i0) → 𝒜 ul (p i) k
    k (i = i0) → 𝒜 ul (q j) k
    k (i = i1) → 𝒜 ul (r j) k
    k (j = i1) → 𝒜 ul (s i) k
    k (k = i0) → ul

{-
fill-prop-squareₚ : {A : I → I → Type ℓ} (𝒜 : (i j : I) → IsProp (A i j))
  → {ul : A i0 i0} {ur : A i1 i0} {ll : A i0 i1} {lr : A i1 i1}
  → (p : Path (λ i → A i i0) ul ur) (q : Path (λ j → A i0 j) ul ll) (r : Path (λ j → A i1 j) ur lr) (s : Path (λ i → A i i1) ll lr)
  → SquareP (λ i j → A i j) p q r s
fill-prop-squareₚ 𝒜 p q r s i j = {!comp ? (∂ i ∨ ∂ j) ?!}
-}

fill-set-square : {A : Type ℓ} → IsSet A → {ul ur ll lr : A} (p : ul ≡ ur) (q : ul ≡ ll) (r : ur ≡ lr) (s : ll ≡ lr)
  → ┌ p ┐
    q · r
    └ s ┘
fill-set-square 𝒜 {ul = ul} {ur = ur} {ll = ll} {lr = lr} p q r s i j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (j = i0) → p (i ∧ k)
    k (i = i0) → q j
    k (i = i1) → sq k j
    k (j = i1) → s (i ∧ k)
    k (k = i0) → 𝒜 _ _ q r′ i j
  where
    sq : (k : I) → p k ≡ s k
    sq k j = hfill (∂ j) (λ { k′ (j = i0) → p (~ k′) ; k′ (j = i1) → s (~ k′) ; k′ (k′ = i0) → r j }) (~ k)
    r′ : ul ≡ ll
    r′ = sq i0

prop-to-set : {A : Type ℓ} → IsProp A → IsSet A
prop-to-set 𝒜 x y p q = fill-prop-square 𝒜 refl p q refl

opaque
  prop-type-set : ∀ {ℓ} → IsSet (PropType ℓ)
  prop-type-set (A , A-prop) (B , B-prop) p q i j =
    P j i , set-fill {A = λ i j → IsProp (P j i)} (λ _ _ → prop-to-set is-prop-prop) i j
      λ where
        i j (j = i0) → A-prop
        i j (i = i0) → snd (p j)
        i j (i = i1) → snd (q j)
        i j (j = i1) → B-prop
    where
      p₀ : A ≡ B
      p₀ j = fst (p j)
      q₀ : A ≡ B
      q₀ j = fst (q j)
      module _ (j : I) where
        f : p₀ j → q₀ j
        f = transport (λ t → p₀ (j ∧ t) → q₀ (j ∧ t)) id
        g : q₀ j → p₀ j
        g = transport (λ t → q₀ (j ∧ t) → p₀ (j ∧ t)) id
        e : p₀ j ≅ q₀ j
        fun e = f
        linv (is-equiv e) = g
        rinv (is-equiv e) = g
        is-linv (is-equiv e) i x = transport (λ t → IsProp (p₀ (j ∧ t))) A-prop (g (f x)) x i
        is-rinv (is-equiv e) i x = transport (λ t → IsProp (q₀ (j ∧ t))) A-prop (f (g x)) x i
        P : p₀ j ≡ q₀ j
        P = hcomp (∂ j) λ where
          k (j = i0) → ((λ k → equiv-path $ equiv-equal e ≅-id (λ i x → A-prop (fun e x) x i) k) ■ refl-path-equiv A) k
          k (k = i0) → equiv-path e
          k (j = i1) → ((λ k → equiv-path $ equiv-equal e ≅-id (λ i x → B-prop (fun e x) x i) k) ■ refl-path-equiv B) k

{-
prop-type-set : ∀ {ℓ} → IsSet (PropType ℓ)
prop-type-set (A , 𝒜) (B , ℬ) p q = Σ-path² (λ i j → α j i) (fill-prop-squareₚ (λ _ _ → is-prop-prop) refl {!dprop (λ i → IsProp (fst (p i))) is-prop-prop 𝒜 ℬ!} {!!} refl)
  where
    α : (j : I) → fst (p j) ≡ fst (q j)
    α j i = transport-inj₁ (λ j → fst (p j)) (λ j → fst (q j)) (fn-path (λ _ → ℬ _ _)) i j
-}

pi-prop : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} → ((x : A) → IsProp (B x)) → IsProp (Π B)
pi-prop B-prop f g i x = B-prop x (f x) (g x) i

pi-set : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} → ((x : A) → IsSet (B x)) → IsSet (Π B)
pi-set B-set f g α β i j x = B-set x (f x) (g x) (λ j → α j x) (λ j → β j x) i j

pi-ntype : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} (h : ℕ) → ((x : A) → IsNType h (B x)) → IsNType h (Π B)
pi-ntype zero = pi-prop
pi-ntype (succ h) B-ntype f g =
  transport (λ t → IsNType h (pi-path-char f g (~ t)))
    (pi-ntype h λ x → B-ntype x (f x) (g x))

fun-prop : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → IsProp B → IsProp (A → B)
fun-prop B-prop = pi-prop (λ _ → B-prop)

fun-set : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → IsSet B → IsSet (A → B)
fun-set B-set = pi-set (λ _ → B-set)

fun-ntype : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} (h : ℕ) → IsNType h B → IsNType h (A → B)
fun-ntype h B-ntype = pi-ntype h (λ _ → B-ntype)
