{-# OPTIONS --cubical --prop #-}
module Path where

open import Cubical.Core.Everything renaming (_,_ to _,,_) public
open import Cubical.Foundations.Equiv.Base using (idEquiv)
open import Cubical.Foundations.Isomorphism
open import Prelude

ExplicitPath : {A : Type} (x y : A) → x ≡ y → x ≡ y
ExplicitPath _ _ p = p

syntax ExplicitPath x y p = x ⟪ p ⟫ y

infix 1 ExplicitPath

dpath : ∀ {ℓ} {A B : Type ℓ} (P : A ≡ B) → A → B → Type ℓ
dpath P = PathP (λ i → P i)

syntax dpath P x y = x =⟦ P ⟧= y

mk-path : ∀ {ℓ} {A : Type ℓ} (p : I → A) → p i0 ≡ p i1
mk-path p i = p i

syntax mk-path (λ i → p) = i ⊢ p

infix 0 mk-path

at : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → I → A
at p i = p i

id : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡ x
id {x = x} _ = x

syntax id {x = x} = ⟪ x ⟫

inv : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
inv p i = p (~ i)

∘-bounds : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → (i : I) (h : I) → Partial (i ∨ ~ i) A
∘-bounds p q i h (i = i0) = p (~ h)
∘-bounds p q i h (i = i1) = q h

∘-base : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → I → A
∘-base {y = y} _ _ _ = y

∘-boundsₚ : ∀ {ℓ} {A B C : Type ℓ} {P : A ≡ B} {Q : B ≡ C} {x : A} {y : B} {z : C} → x =⟦ P ⟧= y → y =⟦ Q ⟧= z → (i : I) (h : I) → PartialP (i ∨ ~ i) (∘-bounds P Q i h)
∘-boundsₚ p q i h (i = i0) = p (~ h)
∘-boundsₚ p q i h (i = i1) = q h

_∘_ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(p ∘ q) i = hcomp (∘-bounds p q i) (∘-base p q i)
{-
(p ∘ q) i =
  hcomp (λ h → λ { (i = i0) → p (~ h)
                 ; (i = i1) → q h }) (p i1)
-}

infixr 10 _∘_

∘-fill : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ h → p (~ h) ≡ q h) id (p ∘ q)
∘-fill p q h i = hfill (∘-bounds p q i) (inS (∘-base p q i)) h

_~∘_ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → y ≡ x → y ≡ z → x ≡ z
p ~∘ q = inv p ∘ q

infixr 10 _~∘_

_∘~_ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → z ≡ y → x ≡ z
p ∘~ q = p ∘ inv q

infixr 10 _∘~_

_∘₃_∘₃_ : ∀ {ℓ} {A : Type ℓ} {x y z w : A} → x ≡ y → y ≡ z → z ≡ w → x ≡ w
(p ∘₃ q ∘₃ r) i =
  hcomp (λ h → λ { (i = i0) → p (~ h)
                 ; (i = i1) → r h }) (q i)

infixr 10 _∘₃_∘₃_

∘-id-left : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → id ∘ p ≡ p
∘-id-left p i j =
  hcomp (λ h → λ { (j = i0) → p i0
                 ; (j = i1) → p h
                 ; (i = i1) → p (j ∧ h) }) (p i0)

∘-inv-left : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → inv p ∘ p ≡ id
∘-inv-left p i j =
  hcomp (λ h → λ { (j = i0) → p (h ∨ i)
                 ; (j = i1) → p (h ∨ i)
                 ; (i = i1) → p i1 }) (p i)

∘-inv-right : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∘ inv p ≡ id
∘-inv-right p = ∘-inv-left (inv p)

∘-∘₃-left : {A : Type} {x y z : A} (p : x ≡ y) (q : y ≡ z) → inv q =⟦( λ i → (p ∘ q) (~ i) ≡ p (~ i) )⟧= id
∘-∘₃-left p q i j =
  hcomp (λ h → λ { (i = i0) → q (h ∧ ~ j)
                 ; (i = i1) → p (~ h)
                 ; (j = i1) → p (~ h ∨ ~ i) }) (p i1)

∘-assoc : {A : Type} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → (p ∘ q) ∘ r ≡ p ∘ (q ∘ r)
∘-assoc {x = x} {w = w} p q r = α ∘ β
  where
    α : (p ∘ q) ∘ r ≡ p ∘₃ q ∘₃ r
    α i j = hcomp (λ h → λ { (j = i0) → ∘-∘₃-left p q h i
                           ; (j = i1) → r h }) (q (~ i ∨ j))
    β : p ∘₃ q ∘₃ r ≡ p ∘ (q ∘ r)
    β i j = hcomp (λ h → λ { (j = i1) → ∘-∘₃-left (inv r) (inv q) h (~ i)
                           ; (j = i0) → p (~ h) }) (q (~ i ∧ j))

invₚ : {A B : Type} {P : A ≡ B} {x : A} {y : B} → x =⟦ P ⟧= y → y =⟦ inv P ⟧= x
invₚ p i = p (~ i)

_∘ₚ_ : {A B C : Type} {P : A ≡ B} {Q : B ≡ C} {x : A} {y : B} {z : C} → x =⟦ P ⟧= y → y =⟦ Q ⟧= z → x =⟦ P ∘ Q ⟧= z
_∘ₚ_ {P = P} {Q = Q} p q i =
  comp (hfill (∘-bounds P Q i) (inS (∘-base P Q i)))
    (λ h → λ { (i = i0) → p (~ h)
             ; (i = i1) → q h }) (p i1)

infixr 10 _∘ₚ_

∘-≡-square : ∀ {ℓ} {A : Type ℓ} {x x′ y y′ : A} (p : x ≡ y) (q : x ≡ x′) (p′ : x′ ≡ y′) (q′ : y ≡ y′) → p ∘ q′ ≡ q ∘ p′ → p =⟦( λ i → q i ≡ q′ i )⟧= p′
∘-≡-square {A} p q p′ q′ α i j =
  hcomp (λ h → λ { (j = i0) → q (h ∧ i)
                 ; (j = i1) → q′ (~ h ∨ i)
                 ; (i = i0) → hcomp (λ k → λ { (j = i0) → p (~ k ∧ h)
                                             ; (j = i1) → q′ (~ h)
                                             ; (h = i0) → (p ∘ q′) j
                                             ; (h = i1) → p (~ k ∨ j) }) (∘-fill p q′ (~ h) j)
                 ; (i = i1) → hcomp (λ k → λ { (j = i0) → q h
                                             ; (j = i1) → p′ (k ∨ ~ h)
                                             ; (h = i0) → (q ∘ p′) j
                                             ; (h = i1) → p′ (k ∧ j) }) (∘-fill q p′ (~ h) j) }) (α i j)

{-
∘ₚ-id-left : {A B C : Type} {P : A ≡ B} {x : A} {y : B} → (p : x =⟦ P ⟧= y) → {!dpath !}
-- {!id ∘ₚ p =⟦( λ i →  x =⟦( λ j → ∘-id-left P (i ∨ j) )⟧= y )⟧= p!} -- {!id ∘ₚ p =⟦( λ i → dpath (∘-id-left P i) x y )⟧= p!} -- id ∘ₚ p =⟦ ? ⟧= p
-- x =⟦ id ∘ P ⟧= y
-- x =⟦ P ⟧= y
∘ₚ-id-left = {!!}
-}

{-
∘ₚ-inv-left : {A B : Type} {P : A ≡ B} {x : A} {y : B} (p : x =⟦ P ⟧= y) → {!invₚ p ∘ₚ p!} =⟦ (λ i → ∘-inv-left P i ≡ id) ⟧= {!!}  -- invₚ p ∘ₚ p =⟦ ∘-inv-left  ⟧= id
∘ₚ-inv-left = {!!}
-}

fun-ext : ∀ {ℓ} {A B : Type ℓ} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
fun-ext p i x = p x i

cong : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
cong f p i = f (p i)

path-ind : {A : Type} (P : (x y : A) → x ≡ y → Type) → (∀ x → P x x id) → {x y : A} (p : x ≡ y) → P x y p
path-ind P f p = transp (λ t → P _ _ (λ i → p (t ∧ i))) i0 (f _)

∘-assoc′ : {A : Type} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → (p ∘ q) ∘ r ≡ p ∘ (q ∘ r)
∘-assoc′ p q r =
  path-ind (λ x y p → ∀ {z w} (q : y ≡ z) (r : z ≡ w) → (p ∘ q) ∘ r ≡ p ∘ (q ∘ r)) (λ x q r → (λ i → ∘-id-left q i ∘ r) ∘ (λ i → ∘-id-left (q ∘ r) (~ i))) p q r

eckmann-hilton : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : ⟪ x ⟫ ≡ ⟪ x ⟫) → p =⟦ i ⊢ q i ≡ q i ⟧= p
eckmann-hilton {x = x} p q i j k =
  hcomp (λ h → λ { (i = i0) → p j (h ∧ k)
                 ; (i = i1) → p j (h ∧ k)
                 ; (j = i0) → q i (~ h ∨ k)
                 ; (j = i1) → q i (~ h ∨ k)
                 ; (k = i0) → q i (~ h)
                 ; (k = i1) → p j h }) x

_∘²_ : ∀ {ℓ} {A : Type ℓ} {x : A} → ⟪ x ⟫ ≡ ⟪ x ⟫ → ⟪ x ⟫ ≡ ⟪ x ⟫ → ⟪ x ⟫ ≡ ⟪ x ⟫
(p ∘² q) i = eckmann-hilton p q i i

sibling : ∀ {ℓ} {A : Type ℓ} → A → A
sibling {A = A} x = hcomp (λ _ → empty) x

sibling-path : ∀ {ℓ} {A : Type ℓ} (x : A) → sibling x ≡ x
sibling-path x i =
  hcomp (λ _ → λ { (i = i1) → x }) x

id-equiv : ∀ {ℓ} {A : Type ℓ} → A ≃ A
fst id-equiv x = x
fst (fst (equiv-proof (snd id-equiv) y)) = y
snd (fst (equiv-proof (snd id-equiv) y)) = id
snd (equiv-proof (snd id-equiv) y) (y′ ,, p) i = p (~ i) ,, λ j → p (~ i ∨ j)

univ : {A B : Type} → A ≃ B → A ≡ B
univ {A} {B} e i = Glue B λ { (i = i0) → A ,, e
                            ; (i = i1) → B ,, idEquiv _ }

{-
univ-intro : {A B : Type} → (e : A ≃ B) → B → (i : I) → univ e i
univ-intro {A} {B} e x i = {!glue (λ { (i = i0) → ? ; (i = i1) → x }) x!}
-}

transport : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
transport p = transp (at p) i0

transport-path : ∀ {A B : Type} (p : A ≡ B) (x : A) → x =⟦( i ⊢ p i )⟧= transport p x
transport-path p x i = transp (λ t → p (t ∧ i)) (~ i) x 

transport-id : ∀ {ℓ} {A : Type ℓ} (x : A) → transport id x ≡ x
transport-id {A = A} x i = transp (λ t → A) i x

transport-∘ : ∀ {ℓ} {A B C : Type ℓ} (p : A ≡ B) (q : B ≡ C) (x : A) → transport (p ∘ q) x ≡ transport q (transport p x)
transport-∘ p q x i = transport q (transport-id (transport p x) i)

transport-equiv : ∀ {A B : Type} (p : A ≡ B) → A ≃ B
transport-equiv {A} {B} p = isoToEquiv φ
  where
    φ : Iso A B
    Iso.fun φ = transport p
    Iso.inv φ = transport (inv p)
    Iso.rightInv φ x =
      inv (transport-∘ (inv p) p x) ∘
      (i ⊢ transport (∘-inv-left p i) x) ∘
      transport-id x
    Iso.leftInv φ x =
      inv (transport-∘ p (inv p) x) ∘
      (i ⊢ transport (∘-inv-right p i) x) ∘
      transport-id x

{-
transport-equiv-path : ∀ {A B : Type} (p : A ≡ B) → univ (transport-equiv p) ≡ p
transport-equiv-path p = {!!}
-}

transport-const : ∀ {ℓ} {A : Type ℓ} (x : A) → transport (λ _ → A) x ≡ x
transport-const {A = A} x i = transp (λ _ → A) i x

transport-inj : ∀ {A B : Type} (p q : A ≡ B) → transport p ≡ transport q → p ≡ q
transport-inj p q α = trust-me
  where
    postulate
      trust-me : p ≡ q

transport-embed : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x y : A) → transport p x ≡ transport p y → x ≡ y
transport-embed p x y q =
  inv (transport-id x) ∘
  (λ i → transport (∘-inv-right p (~ i)) x) ∘
  transport-∘ p (inv p) x ∘
  (λ i → transport (inv p) (q i)) ∘
  inv (transport-∘ p (inv p) y) ∘
  (λ i → transport (∘-inv-right p i) y) ∘
  transport-id y

abstract
  iso-path : ∀ {ℓ} {A B : Type ℓ} → Iso A B → A ≡ B
  iso-path {A = A} {B = B} φ i = Glue B λ { (i = i0) → A ,, isoToEquiv φ
                                          ; (i = i1) → B ,, id-equiv }

  to-iso-path : ∀ {ℓ} {A B : Type ℓ} (φ : Iso A B) → (a : A) → PathP (λ i → iso-path φ i) a (Iso.fun φ a)
  to-iso-path {A = A} {B = B} φ a i =
    glue (λ { (i = i0) → a
            ; (i = i1) → Iso.fun φ a })
      (Iso.fun φ a)

  transport-iso : ∀ {ℓ} {A B : Type ℓ} (φ : Iso A B) → transport (iso-path φ) ≡ Iso.fun φ
  transport-iso φ i x = transport-const (Iso.fun φ x) i

as-iso : ∀ {ℓ′} (A : Type ℓ′) ℓ → Iso A (A as ℓ)
Iso.fun (as-iso A ℓ) = promote
Iso.inv (as-iso A ℓ) = demote
Iso.rightInv (as-iso A ℓ) _ = id
Iso.leftInv (as-iso A ℓ) _ = id

as-equiv : ∀ {ℓ′} (A : Type ℓ′) ℓ → A ≃ A as ℓ
as-equiv A ℓ = isoToEquiv (as-iso A ℓ)
