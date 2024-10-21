{-# OPTIONS --cubical --prop #-}
module Semigroup where

open import Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Base using (idEquiv)
open import Logic
open import Product using (_×_; _,_; fst; snd)
import Product as P
open import List using (List; []; _∷_)
import List as L
open import Circle using (S¹; base; loop)
open import String
open import Show

data Free (A : Type) : Type
data Can {A} : Free A → Type

data Free A where
  ⟨_⟩ : A → Free A
  _·_ : Free A → Free A → Free A
  ⟨_⟩·₃_·₃_ : ∀ {y z} a (yᶜ : ♯ ♭ Can y) (zᶜ : ♯ ♭ Can z) → (⟨ a ⟩ · y) · z ≡ ⟨ a ⟩ · (y · z)
  -- ⟨_⟩·₃_·₃_ : ∀ a y z → (⟨ a ⟩ · y) · z ≡ ⟨ a ⟩ · (y · z)
  -- comm : ∀ {a b} (p : a ≡ b) y z → ⟨ a ⟩·₃ y ·₃ z =⟦( λ i → (⟨ p i ⟩ · y) · z ≡ ⟨ p i ⟩ · (y · z) )⟧= ⟨ b ⟩·₃ y ·₃ z

infix 60 _·_ ⟨_⟩·₃_·₃_

pattern ⟨_⟩·₃_·₃_∶_ a y z i = (⟨ a ⟩·₃ y ·₃ z) i

data Can where
  ⟨_⟩ᶜ : ∀ a → Can ⟨ a ⟩
  ⟨_⟩·ᶜ_ : ∀ a {y} → Can y → Can (⟨ a ⟩ · y)

uncan : ∀ {A} {x : Free A} → Can x → Free A
uncan {x = x} _ = x

neq-⟨⟩-· : ∀ {A} {a : A} {x y} → ⟨ a ⟩ ≢ x · y
neq-⟨⟩-· {A} p = proof (transport (t ⊢ T (p t)) (lift top))
  where
    T : Free A → Type
    T ⟨ _ ⟩ = ♯ ⊤
    T (_ · _) = ♯ ⊥
    T (⟨ _ ⟩·₃ _ ·₃ _ ∶ _) = ♯ ⊥

{-
neq-⟨⟩-assoc : ∀ {A} {a : A} {b x y} (i : I) → ⟨ a ⟩ ≢ ⟨ b ⟩·₃ x ·₃ y ∶ i
neq-⟨⟩-assoc {A} i p = proof (transport (t ⊢ T (p t)) (lift top))
  where
    T : Free A → Type
    T ⟨ _ ⟩ = ♯ ⊤
    T (_ · _) = ♯ ⊥
    T (⟨ _ ⟩·₃ _ ·₃ _ ∶ _) = ♯ ⊥

from-⟨⟩ : ∀ {A} {a : A} {x : Free A} → ⟨ a ⟩ ≡ x → A
from-⟨⟩ {x = ⟨ b′ ⟩} q = b′
from-⟨⟩ {x = x · y} q = ⊥-elim (neq-⟨⟩-· q)
from-⟨⟩ {x = ⟨ b′ ⟩·₃ x ·₃ y ∶ i} q = ⊥-elim (neq-⟨⟩-assoc i q )

⟨⟩-inj : ∀ {A} {a b : A} → ⟨ a ⟩ ≡ ⟨ b ⟩ → a ≡ b
⟨⟩-inj {A} {a} p i = from-⟨⟩ (λ t → p (t ∧ i))

⟨⟩-path-shape : ∀ {A} {a b : A} (p : ⟨ a ⟩ ≡ ⟨ b ⟩) → p ≡ (i ⊢ ⟨ ⟨⟩-inj p i ⟩)
⟨⟩-path-shape p i = {!!}

⟨⟩-embed : ∀ {A} {a b : A} → (⟨ a ⟩ ≡ ⟨ b ⟩) ≡ (a ≡ b)
⟨⟩-embed {A} {a} {b} = isoToPath φ
  where
    φ : Iso (⟨ a ⟩ ≡ ⟨ b ⟩) (a ≡ b)
    Iso.fun φ = ⟨⟩-inj
    Iso.inv φ p i = ⟨ p i ⟩
    Iso.rightInv φ p = id
    Iso.leftInv φ p = {!!}
-}

{-
Can-prop′ : ∀ {A} {x x′ : Free A} (p : x ≡ x′) (c : Can x) (c′ : Can x′) → c =⟦ i ⊢ Can (p i) ⟧= c′
Can-prop′ p ⟨ a ⟩ᶜ ⟨ b ⟩ᶜ i = {!⟨ ⟨⟩-inj p i ⟩ᶜ!}
Can-prop′ p ⟨ a ⟩ᶜ (⟨ b ⟩·ᶜ c′) = ⊥-elim (neq-⟨⟩-· p)
Can-prop′ p (⟨ a ⟩·ᶜ c) ⟨ b ⟩ᶜ = ⊥-elim (neq-⟨⟩-· (inv p))
Can-prop′ p (⟨ a ⟩·ᶜ c) (⟨ b ⟩·ᶜ c′) = {!!}

Can-prop : ∀ {A} {x : Free A} → is-prop (Can x)
Can-prop = Can-prop′ id
-}

_·ᶜ_ : ∀ {A} {x y : Free A} → Can x → Can y → Can (x · y)
⟨ a ⟩ᶜ ·ᶜ yᶜ = ⟨ a ⟩·ᶜ yᶜ
(⟨ a ⟩·ᶜ xᶜ) ·ᶜ yᶜ = transp (λ t → Can (⟨ a ⟩·₃ ∣ xᶜ ∣ ·₃ ∣ yᶜ ∣ ∶ ~ t)) i0 (⟨ a ⟩·ᶜ (xᶜ ·ᶜ yᶜ))

can : ∀ {A} (x : Free A) → Can x
can ⟨ a ⟩ = ⟨ a ⟩ᶜ
can (x · y) = can x ·ᶜ can y
can (⟨_⟩·₃_·₃_ {y = x} {z = y} a xᶜ yᶜ i) =
  transport-path (λ t → Can (⟨ a ⟩·₃ ∣ can x ∣ ·₃ ∣ can y ∣ ∶ ~ t)) (⟨ a ⟩·ᶜ (can x ·ᶜ can y)) (~ i)
  -- transp (λ t → Can (⟨ a ⟩·₃ Can-prop (can x) xᶜ t ·₃ Can-prop (can y) yᶜ t ∶ i)) (i ∨ ~ i) (p (~ i)) 
-- can (comm p x y i j) = {!!}

_·ᶜ₃_·ᶜ₃_ : ∀ {A} {x y z : Free A} → Can x → Can y → Can z → (x · y) · z ≡ x · (y · z)

⟨ a ⟩ᶜ ·ᶜ₃ yᶜ ·ᶜ₃ zᶜ = ⟨ a ⟩·₃ ∣ yᶜ ∣ ·₃ ∣ zᶜ ∣
(⟨ a ⟩·ᶜ xᶜ) ·ᶜ₃ yᶜ ·ᶜ₃ zᶜ =
  (i ⊢ (⟨ a ⟩·₃ ∣ xᶜ ∣ ·₃ ∣ yᶜ ∣) i · uncan zᶜ) ∘
  (⟨ a ⟩·₃ ∣ xᶜ ·ᶜ yᶜ ∣ ·₃ ∣ zᶜ ∣) ∘
  (i ⊢ ⟨ a ⟩ · (xᶜ ·ᶜ₃ yᶜ ·ᶜ₃ zᶜ) i) ∘
  (i ⊢ (⟨ a ⟩·₃ ∣ xᶜ ∣ ·₃ ∣ yᶜ ·ᶜ zᶜ ∣) (~ i))

_·₃_·₃_ : ∀ {A} (x y z : Free A) → (x · y) · z ≡ x · (y · z)
x ·₃ y ·₃ z = can x ·ᶜ₃ can y ·ᶜ₃ can z

{-
a(b(c(de))) = (ab)(c(de)) = (ab)((cd)e)
a(b(c(de))) = a(b((cd)e)) = a((b(cd))e) = (a(b(cd)))e = (a((bc)d))e = ((a(bc))d)e = (((ab)c)d)e
-}

cons : ∀ {A} → A × List A → List A
cons (x , xs) = x ∷ xs

to-listᶜ : ∀ {A} {x : Free A} → Can x → A × List A
to-listᶜ ⟨ a ⟩ᶜ = a , []
to-listᶜ (⟨ a ⟩·ᶜ xᶜ) = a , cons (to-listᶜ xᶜ)

to-list : ∀ {A} → Free A → A × List A
to-list x = to-listᶜ (can x)

from-list′ : ∀ {A} → A → List A → Free A
from-list′ a [] = ⟨ a ⟩
from-list′ a (b ∷ xs) = ⟨ a ⟩ · from-list′ b xs

from-listᶜ : ∀ {A} (a : A) (xs : List A) → Can (from-list′ a xs)
from-listᶜ a [] = ⟨ a ⟩ᶜ
from-listᶜ a (b ∷ xs) = ⟨ a ⟩·ᶜ from-listᶜ b xs

from-list : ∀ {A} → A × List A → Free A
from-list (a , xs) = from-list′ a xs

to-fromᶜ : ∀ {A} (a : A) (xs : List A) → to-listᶜ (can (from-list′ a xs)) ≡ (a , xs)
to-fromᶜ a [] = id
to-fromᶜ a (b ∷ xs) i = a , cons (to-fromᶜ b xs i)

from-toᶜ : ∀ {A} (a : A) {x : Free A} (xᶜ : Can x) → from-list′ a (cons (to-listᶜ xᶜ)) ≡ ⟨ a ⟩ · x
from-toᶜ a ⟨ b ⟩ᶜ = id
from-toᶜ a (⟨ b ⟩·ᶜ xᶜ) i = ⟨ a ⟩ · from-toᶜ b xᶜ i

to-from : ∀ {A} (xs : A × List A) → to-list (from-list xs) ≡ xs
to-from (a , xs) = to-fromᶜ a xs 

from-to : ∀ {A} (x : Free A) → from-list (to-list x) ≡ x
from-to x with can x
from-to .(⟨ a ⟩) | ⟨ a ⟩ᶜ = id
from-to .(⟨ a ⟩ · _) | ⟨ a ⟩·ᶜ xᶜ = from-toᶜ a xᶜ

list-path : ∀ A → Free A ≡ A × List A
list-path A = isoToPath φ
  where
    φ : Iso (Free A) (A × List A)
    Iso.fun φ = to-list
    Iso.inv φ = from-list
    Iso.rightInv φ = to-from
    Iso.leftInv φ = from-to

normalise-path : ∀ A → Free A ≡ Free A
normalise-path A = list-path A ∘ inv (list-path A)

{-
test : transport (normalise-path String) ((⟨ "a" ⟩ · ⟨ "b" ⟩) · ⟨ "c" ⟩) ≡ ⟨ "a" ⟩ · (⟨ "b" ⟩ · ⟨ "c" ⟩)
test = id
-}

foo : ⟨ base ⟩ · (⟨ base ⟩ · ⟨ base ⟩) ≡ ⟨ base ⟩ · (⟨ base ⟩ · ⟨ base ⟩)
foo i =
  hcomp (λ h → λ { (i = i0) → ⟨ base ⟩·₃ ∣ ⟨ base ⟩ᶜ ∣ ·₃ ∣ ⟨ base ⟩ᶜ ∣ ∶ h
                 ; (i = i1) → ⟨ base ⟩·₃ ∣ ⟨ base ⟩ᶜ ∣ ·₃ ∣ ⟨ base ⟩ᶜ ∣ ∶ h }) ((⟨ loop i ⟩ · ⟨ base ⟩) · ⟨ base ⟩)

elem : S¹ × List S¹
elem = base , base ∷ base ∷ []

bar : elem ≡ elem
bar i = to-list (foo i)

bar₁ : base ≡ base
bar₁ i = fst (bar i)

bar₂ : base ∷ base ∷ [] ≡ base ∷ base ∷ []
bar₂ i = snd (bar i)

bar₂′ : base ∷ base ∷ [] L.∼ base ∷ base ∷ []
bar₂′ = L.encode bar₂

base-assoc : (⟨ base ⟩ · ⟨ base ⟩) · ⟨ base ⟩ ≡ ⟨ base ⟩ · (⟨ base ⟩ · ⟨ base ⟩)
base-assoc = ⟨ base ⟩·₃ ∣ ⟨ base ⟩ᶜ ∣ ·₃ ∣ ⟨ base ⟩ᶜ ∣

Cheat : (A A′ B C : Type) → A ≡ A′ → (x : Free S¹) → ♯ ¬¬ (x ≡ ⟨ base ⟩ · (⟨ base ⟩ · ⟨ base ⟩)) → Type
Cheat A A′ B C P ⟨ _ ⟩ p = {!!}
Cheat A A′ B C P (⟨ _ ⟩ · ⟨ _ ⟩) p = {!!}
Cheat A A′ B C P (⟨ a ⟩ · (⟨ b ⟩ · ⟨ c ⟩)) p = A′ × (B × C)
Cheat A A′ B C P (⟨ a ⟩ · (⟨ b ⟩ · (_ · _))) p = {!!}
Cheat A A′ B C P (⟨ a ⟩ · (⟨ b ⟩ · (⟨ _ ⟩·₃ _ ·₃ _ ∶ _))) p = {!!}
Cheat A A′ B C P (⟨ a ⟩ · ((_ · _) · _)) p = {!!}
Cheat A A′ B C P (⟨ a ⟩ · ((⟨ _ ⟩·₃ _ ·₃ _ ∶ _) · _)) p = {!!}
Cheat A A′ B C P (⟨ _ ⟩ · (⟨ _ ⟩·₃ _ ·₃ _ ∶ _)) p = {!!}
Cheat A A′ B C P ((⟨ a ⟩ · ⟨ b ⟩) · ⟨ c ⟩) p = (A × B) × C
Cheat A A′ B C P ((⟨ a ⟩ · ⟨ b ⟩) · (_ · _)) p = {!!}
Cheat A A′ B C P ((⟨ a ⟩ · ⟨ b ⟩) · (⟨ _ ⟩·₃ _ ·₃ _ ∶ _)) p = {!!}
Cheat A A′ B C P ((⟨ a ⟩ · (_ · _)) · _) p = {!!}
Cheat A A′ B C P ((⟨ a ⟩ · (⟨ _ ⟩·₃ _ ·₃ _ ∶ _)) · z) p = {!!}
Cheat A A′ B C P (((_ · _) · _) · _) p = {!!}
Cheat A A′ B C P (((⟨ a ⟩·₃ _ ·₃ _ ∶ i) · _) · _) p = {!!}
Cheat A A′ B C P ((⟨ _ ⟩·₃ _ ·₃ _ ∶ _) · _) p = {!!}
Cheat A A′ B C P (⟨_⟩·₃_·₃_ {y = ⟨ b ⟩} {z = ⟨ c ⟩} a _ _ i) p = (P.×-assoc A B C ∘ (λ j → P j × (B × C))) i
Cheat A A′ B C P (⟨_⟩·₃_·₃_ {y = ⟨ _ ⟩} {z = _ · _} a _ _ i) p = {!!}
Cheat A A′ B C P (⟨_⟩·₃_·₃_ {y = ⟨ _ ⟩} {z = ⟨ _ ⟩·₃ _ ·₃ _ ∶ _} _ _ _ i) p = {!!}
Cheat A A′ B C P (⟨_⟩·₃_·₃_ {y = _ · _} {z = z} _ _ _ i) p = {!!}
Cheat A A′ B C P (⟨_⟩·₃_·₃_ {y = ⟨ _ ⟩·₃ _ ·₃ _ ∶ _} {z = z} _ _ _ i) p = {!!}

cheat₁ : (A A′ B C : Type) → A ≡ A′ → ((A × B) × C) ≡ (A′ × (B × C))
cheat₁ A A′ B C P i = Cheat A A′ B C P (base-assoc i)
  (lift λ np → np ((j ⊢ base-assoc (~ j ∧ i)) ∘ base-assoc))

cheat₃ : (A A′ B C : Type) → A ≡ A′ → (A × (B × C)) ≡ (A′ × (B × C))
cheat₃ A A′ B C P i = {!Cheat A A′ B C P (⟨ loop i ⟩ · (⟨ base ⟩ · ⟨ base ⟩)) ? !}

cheat : ∀ {A A′ B C} → A ≡ A′ → (⟨ base ⟩ · ⟨ base ⟩) · ⟨ base ⟩ ≡ ⟨ base ⟩ · (⟨ base ⟩ · ⟨ base ⟩) → ((A × B) × C) ≡ (A′ × (B × C))
cheat {A} {A′} {B} {C} P q i = f (q i) ∣ j ⊢ q (i ∨ j) ∣ 
  where
    f : (x : Free S¹) → ♯ ♭ (x ≡ ⟨ base ⟩ · (⟨ base ⟩ · ⟨ base ⟩)) → Type
    f ⟨ _ ⟩ p = {!!}
    f (⟨ _ ⟩ · ⟨ _ ⟩) p = {!!}
    f (⟨ a ⟩ · (⟨ b ⟩ · ⟨ c ⟩)) p = A′ × (B × C)
    f (⟨ a ⟩ · (⟨ b ⟩ · (_ · _))) p = {!!}
    f (⟨ a ⟩ · (⟨ b ⟩ · (⟨ _ ⟩·₃ _ ·₃ _ ∶ _))) p = {!!}
    f (⟨ a ⟩ · ((_ · _) · _)) p = {!!}
    f (⟨ a ⟩ · ((⟨ _ ⟩·₃ _ ·₃ _ ∶ _) · _)) p = {!!}
    f (⟨ _ ⟩ · (⟨ _ ⟩·₃ _ ·₃ _ ∶ _)) p = {!!}
    f ((⟨ a ⟩ · ⟨ b ⟩) · ⟨ c ⟩) p = (A × B) × C
    f ((⟨ a ⟩ · ⟨ b ⟩) · (_ · _)) p = {!!}
    f ((⟨ a ⟩ · ⟨ b ⟩) · (⟨ _ ⟩·₃ _ ·₃ _ ∶ _)) p = {!!}
    f ((⟨ a ⟩ · (_ · _)) · _) p = {!!}
    f ((⟨ a ⟩ · (⟨ _ ⟩·₃ _ ·₃ _ ∶ _)) · z) p = {!!}
    f (((_ · _) · _) · _) p = {!!}
    f (((⟨ a ⟩·₃ _ ·₃ _ ∶ i) · _) · _) p = {!!}
    f ((⟨ _ ⟩·₃ _ ·₃ _ ∶ _) · _) p = {!!}
    f (⟨_⟩·₃_·₃_ {y = ⟨ b ⟩} {z = ⟨ c ⟩} a _ _ i) p = (P.×-assoc A B C ∘ (λ j → P j × (B × C))) i
    f (⟨_⟩·₃_·₃_ {y = ⟨ _ ⟩} {z = _ · _} a _ _ i) p = {!!}
    f (⟨_⟩·₃_·₃_ {y = ⟨ _ ⟩} {z = ⟨ _ ⟩·₃ _ ·₃ _ ∶ _} _ _ _ i) p = {!!}
    f (⟨_⟩·₃_·₃_ {y = _ · _} {z = z} _ _ _ i) p = ⊥-elim (squash-contra (proof p) λ p → {!p i0!})
    f (⟨_⟩·₃_·₃_ {y = ⟨ _ ⟩·₃ _ ·₃ _ ∶ _} {z = z} _ _ _ i) p = {!!}

cheat′ : ∀ {A A′ B C} → A ≡ A′ → ((A × B) × C) ≡ (A′ × (B × C))
cheat′ P = cheat P base-assoc

devil-square : base-assoc =⟦ i ⊢ (⟨ loop i ⟩ · ⟨ base ⟩) · ⟨ base ⟩ ≡ ⟨ loop i ⟩ · (⟨ base ⟩ · ⟨ base ⟩) ⟧= base-assoc
devil-square i j = {!!}

prepend : ∀ {A} → Free A → List A → List A
prepend ⟨ a ⟩ ys = a ∷ ys
prepend (x · y) ys = prepend x (prepend y ys)
prepend (⟨_⟩·₃_·₃_ {y = x} {z = y} a xᶜ yᶜ _) ys = a ∷ prepend x (prepend y ys)
-- prepend (comm p x₁ x₂ i j) ys = p i ∷ prepend x₁ (prepend x₂ ys)

_∼ᶜ_ : ∀ {A} {x y : Free A} → Can x → Can y → Type
⟨ a ⟩ᶜ ∼ᶜ ⟨ b ⟩ᶜ = a ≡ b
⟨ _ ⟩ᶜ ∼ᶜ (⟨ _ ⟩·ᶜ _) = ♯ ⊥
(⟨ _ ⟩·ᶜ _) ∼ᶜ ⟨ _ ⟩ᶜ = ♯ ⊥
(⟨ a ⟩·ᶜ xᶜ) ∼ᶜ (⟨ b ⟩·ᶜ yᶜ) = (a ≡ b) × (xᶜ ∼ᶜ yᶜ)

_∼_ : ∀ {A} → Free A → Free A → Type
x ∼ y = can x ∼ᶜ can y

∼ᶜ-id : ∀ {A} {x : Free A} (xᶜ : Can x) → xᶜ ∼ᶜ xᶜ
∼ᶜ-id ⟨ a ⟩ᶜ = id
∼ᶜ-id (⟨ a ⟩·ᶜ xᶜ) = id , ∼ᶜ-id xᶜ

encodeᶜ : ∀ {A} {x y : Free A} (xᶜ : Can x) (yᶜ : Can y) {p : x ≡ y} → xᶜ =⟦ i ⊢ Can (p i) ⟧= yᶜ → xᶜ ∼ᶜ yᶜ
encodeᶜ xᶜ yᶜ p = {!transport (t ⊢ p i0 ∼ᶜ ∼ᶜ-id xᶜ!}

encode : ∀ {A} {x y : Free A} → x ≡ y → x ∼ y
encode p = transport (t ⊢ p i0 ∼ p t) (∼ᶜ-id (can (p i0)))

decodeᶜ : ∀ {A} {x y : Free A} (xᶜ : Can x) (yᶜ : Can y) → xᶜ ∼ᶜ yᶜ → x ≡ y
decodeᶜ ⟨ a ⟩ᶜ ⟨ b ⟩ᶜ p i = ⟨ p i ⟩
decodeᶜ ⟨ a ⟩ᶜ (⟨ b ⟩·ᶜ yᶜ) p = ⊥-elim (proof p) 
decodeᶜ (⟨ a ⟩·ᶜ xᶜ) ⟨ b ⟩ᶜ p = ⊥-elim (proof p)
decodeᶜ (⟨ a ⟩·ᶜ xᶜ) (⟨ b ⟩·ᶜ yᶜ) p i = ⟨ fst p i ⟩ · decodeᶜ xᶜ yᶜ (snd p) i

decode : ∀ {A} {x y : Free A} → x ∼ y → x ≡ y
decode = decodeᶜ _ _

{-
encode-decodeᶜ : ∀ {A} {x y : Free A} (xᶜ : Can x) (yᶜ : Can y) (p : xᶜ ∼ᶜ yᶜ) → encodeᶜ xᶜ yᶜ (decodeᶜ xᶜ yᶜ p) ≡ p
encode-decodeᶜ xᶜ yᶜ p = {!!}
-}

{-
_∼_ : ∀ {A} → Free A → Free A → Type
sim : ∀ {A} → Free A → Free A → Free A → Free A → Type

infix 5 _∼_

⟨ a ⟩ ∼ ⟨ b ⟩ = a ≡ b
⟨ a ⟩ ∼ _ · _ = ♯ ⊥
⟨ a ⟩ ∼ ·-assoc-⟨⟩ b y₁ y₂ j = {!!}
_ · _ ∼ ⟨ b ⟩ = ♯ ⊥
x₁ · x₂ ∼ y₁ · y₂ = sim x₁ x₂ y₁ y₂
x₁ · x₂ ∼ ·-assoc-⟨⟩ b y₁ y₂ j = {!!}
·-assoc-⟨⟩ a x₁ x₂ i ∼ y = {!!}

sim ⟨ a ⟩ x₂ ⟨ b ⟩ y₂ = (a ≡ b) × (x₂ ∼ y₂) 
sim ⟨ a ⟩ x₂ (y₁ · y₁′) y₂ = sim ⟨ a ⟩ x₂ y₁ (y₁′ · y₂)
sim ⟨ a ⟩ x₂ (·-assoc-⟨⟩ a₁ y₁ y₃ i) y₂ = {!!}
sim (x₁ · x₁′) x₂ y₁ y₂ = sim x₁ (x₁′ · x₂) y₁ y₂
sim (·-assoc-⟨⟩ a x₁ x₃ i) x₂ y₁ y₂ = {!!}
-}

{-
_·₃_·₃_ : ∀ {A} (x y z : Free A) → (x · y) · z ≡ x · (y · z)
⟨ a ⟩ ·₃ y ·₃ z = ⟨ a ⟩·₃ y ·₃ z
(x₁ · x₂) ·₃ y ·₃ z =
  (λ i → (x₁ ·₃ x₂ ·₃ y) i · z) ∘
  (λ i → (x₁ ·₃ (x₂ · y) ·₃ z) i) ∘
  (λ i → x₁ · (x₂ ·₃ y ·₃ z) i) ∘
  (λ i → (x₁ ·₃ x₂ ·₃ (y · z)) (~ i))
((⟨ a ⟩·₃ x₁ ·₃ x₂ ∶ i) ·₃ y ·₃ z) j = ∘-≡-square α β α′ β′ Δ j i 
  where
    α : (((⟨ a ⟩ · x₁) · x₂) · y) · z ≡ ((⟨ a ⟩ · (x₁ · x₂)) · y) · z
    α i = ((⟨ a ⟩·₃ x₁ ·₃ x₂) i · y) · z
    β : (((⟨ a ⟩ · x₁) · x₂) · y) · z ≡ ((⟨ a ⟩ · x₁) · x₂) · (y · z)
    β = cong (λ w → w · z)
             ((i ⊢ ((⟨ a ⟩·₃ x₁ ·₃ x₂) i · y)) ∘
              (i ⊢ (⟨ a ⟩·₃ (x₁ · x₂) ·₃ y) i) ∘
              (i ⊢ (⟨ a ⟩ · (x₁ ·₃ x₂ ·₃ y) i)) ∘
              (i ⊢ (⟨ a ⟩·₃ x₁ ·₃ (x₂ · y)) (~ i))) ∘
        ((i ⊢ (⟨ a ⟩·₃ x₁ ·₃ (x₂ · y)) i · z) ∘
         (i ⊢ (⟨ a ⟩·₃ (x₁ · (x₂ · y)) ·₃ z) i) ∘
         (i ⊢ ⟨ a ⟩ · (x₁ ·₃ (x₂ · y) ·₃ z) i) ∘
         (i ⊢ (⟨ a ⟩·₃ x₁ ·₃ ((x₂ · y) · z)) (~ i))) ∘
        (i ⊢ (⟨ a ⟩ · x₁) · (x₂ ·₃ y ·₃ z) i) ∘
        inv ((i ⊢ (⟨ a ⟩·₃ x₁ ·₃ x₂) i · (y · z)) ∘
             (i ⊢ (⟨ a ⟩·₃ (x₁ · x₂) ·₃ (y · z)) i) ∘
             (i ⊢ ⟨ a ⟩ · (x₁ ·₃ x₂ ·₃ (y · z)) i) ∘
             (i ⊢ (⟨ a ⟩·₃ x₁ ·₃ (x₂ · (y · z))) (~ i)))
    β-check : β ≡ ((⟨ a ⟩ · x₁) · x₂) ·₃ y ·₃ z
    β-check = id
    α′ : ((⟨ a ⟩ · x₁) · x₂) · (y · z) ≡ (⟨ a ⟩ · (x₁ · x₂)) · (y · z)
    α′ i = (⟨ a ⟩·₃ x₁ ·₃ x₂) i · (y · z)
    β′ : ((⟨ a ⟩ · (x₁ · x₂)) · y) · z ≡ (⟨ a ⟩ · (x₁ · x₂)) · (y · z)
    β′ = (i ⊢ (⟨ a ⟩·₃ (x₁ · x₂) ·₃ y) i · z) ∘
         (i ⊢ (⟨ a ⟩·₃ ((x₁ · x₂) · y) ·₃ z) i) ∘
         cong (λ w → ⟨ a ⟩ · w)
              ((i ⊢ (x₁ ·₃ x₂ ·₃ y) i · z) ∘
               (i ⊢ (x₁ ·₃ (x₂ · y) ·₃ z) i) ∘
               (i ⊢ x₁ · (x₂ ·₃ y ·₃ z) i) ∘
               (i ⊢ (x₁ ·₃ x₂ ·₃ (y · z)) (~ i))) ∘
         (i ⊢ (⟨ a ⟩·₃ (x₁ · x₂) ·₃ (y · z)) (~ i))
    β′-check : β′ ≡ (⟨ a ⟩ · (x₁ · x₂)) ·₃ y ·₃ z
    β′-check = id
    {-
    -- α∘β′: (((a x₁) x₂) y) z = ((a (x₁ x₂)) y) z = (a ((x₁ x₂) y)) z = a (((x₁ x₂) y) z) = a ((x₁ (x₂ y)) z)
                               = a (x₁ ((x₂ y) z)) = a (x₁ (x₂ (y z))) = a ((x₁ x₂) (y z)) = (a (x₁ x₂)) (y z)
    -- β∘α′: (((a x₁) x₂) y) z = ((a (x₁ x₂)) y) z = (a ((x₁ x₂) y)) z = (a (x₁ (x₂ y))) z = ((a x₁) (x₂ y)) z
                               = (a (x₁ (x₂ y))) z = a ((x₁ (x₂ y)) z) = a (x₁ ((x₂ y) z)) = (a x₁) ((x₂ y) z)
                               = (a x₁) (x₂ (y z)) = a (x₁ (x₂ (y z))) = a ((x₁ x₂) (y z)) = (a (x₁ x₂)) (y z)
                               = ((a x₁) x₂) (y z) = (a (x₁ x₂)) (y z)

                               (a ((x₁ x₂) y)) z = a (((x₁ x₂) y) z) = a ((x₁ (x₂ y)) z) = a (x₁ ((x₂ y) z)) = a (x₁ (x₂ (y z)))

                               (a ((x₁ x₂) y)) z = (a (x₁ (x₂ y))) z = ((a x₁) (x₂ y)) z = (a (x₁ (x₂ y))) z = a ((x₁ (x₂ y)) z) = a (x₁ ((x₂ y) z)) = (a x₁) ((x₂ y) z) = (a x₁) (x₂ (y z)) = a (x₁ (x₂ (y z)))
                               -}
    Δ : α ∘ β′ ≡ β ∘ α′
    Δ = {!!}
-}

-- (comm p x₁ x₂ i j) ·₃ y ·₃ z = {!!}

{-
((a · x₁) · x₂) · y · z = ((a · x₁) · x₂ · y) · z ⋯ (a · x₁) · (x₂ · y) · z ⋯ (a · x₁) · (x₂ · y · z) ⋯ ~ (a · x₁) · x₂ · (y · z)
(a · x₁) · x₂ · y = (a · x₁ · x₂) · y ⋯ a · (x₁ · x₂) · y ⋯ a · (x₁ · x₂ · y) ⋯ ~ a · x₁ · (x₂ · y)

((a · x₁) · x₂) · y · z =
  ((a · x₁ · x₂) · y) · z ⋯ (a · (x₁ · x₂) · y) · z ⋯ (a · (x₁ · x₂ · y)) · z ⋯ ~ (a · x₁ · (x₂ · y))) · z ⋯
  (a · x₁) · (x₂ · y) · z ⋯
  (a · x₁) · (x₂ · y · z) ⋯
  ~ (a · x₁) · x₂ · (y · z)

(a · x₁) · x₂ · y = (a · x₁ · x₂) · y ⋯ a · (x₁ · x₂) · y ⋯ a · (x₁ · x₂ · y) ⋯ ~ a · x₁ · (x₂ · y)

(a · (x₁ · x₂)) · y · z =
  (a · (x₁ · x₂) · y) · z ⋯

-}

{-
·-assoc : ∀ {A} (x y z : Free A) → (x · y) · z ≡ x · (y · z)
·-assoc ⟨ a ⟩ y z = ·-assoc-⟨⟩ a y z
·-assoc (x₁ · x₂) y z =
  (λ i → ·-assoc x₁ x₂ y i · z) ∘
  (λ i → ·-assoc x₁ (x₂ · y) z i) ∘₃
  (λ i → x₁ · ·-assoc x₂ y z i) ∘₃
  (λ i → ·-assoc x₁ x₂ (y · z) (~ i))
·-assoc (·-assoc-⟨⟩ a x₁ x₂ i) y z = {!!}
-- i=0 ·-assoc ((⟨ a ⟩ · x₁) · x₂) y z j
-- i=1 ·-assoc (⟨ a ⟩ · (x₁ · x₂)) y z j
-- j=0 (·-assoc-⟨⟩ a x₁ x₂ i · y) · z
-- j=1 ·-assoc-⟨⟩ a x₁ x₂ i · (y · z)
-}

-- A ((⟨ a ⟩ · x₁) · x₂) y z = (A (⟨ a ⟩ · x₂) x₂ y · z) ∘ (·-assoc
-- A (⟨ a ⟩ · (x₁ · x₂)) y z = 

{-
·-assoc-four₁ : ∀ {A} (x y z w : Free A) → ((x · y) · z) · w ≡ x · (y · (z · w))
·-assoc-four₁ x y z w =
  (λ i → ·-assoc x y z i · w) ∘₃
  (λ i → ·-assoc x (y · z) w i) ∘₃
  λ i → x · ·-assoc y z w i

·-assoc-four₂ : ∀ {A} (x y z w : Free A) → ((x · y) · z) · w ≡ x · (y · (z · w))
·-assoc-four₂ x y z w =
  (λ i → ·-assoc (x · y) z w i) ∘
  λ i → ·-assoc x y (z · w) i
-}
