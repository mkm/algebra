{-# OPTIONS --cubical --prop #-}
module Monoid where

open import Path
open import Logic
open import List using (List; []; _∷_)

data Count : Type where
  none : Count
  some : Count

max : Count → Count → Count
max none μ = μ
max some _ = some

max-sym : ∀ μ₁ μ₂ → max μ₁ μ₂ ≡ max μ₂ μ₁
max-sym none none _ = none
max-sym none some _ = some
max-sym some none _ = some
max-sym some some _ = some

data IsSome : Count → Type where
  instance triv : IsSome some

data Free (A : Type) : Type
data Can {A} : Count → Free A → Type

data Free A where
  ⟨_⟩ : A → Free A
  ε : Free A
  _·_ : Free A → Free A → Free A
  ε·ε : ε · ε ≡ ε
  ε·_ : ∀ {y} (yᶜ : ! Can some y) → ε · y ≡ y
  _·ε : ∀ {x} (xᶜ : ! Can some x) → x · ε ≡ x
  ⟨_⟩·₃_·₃_ : ∀ {μ y z} a → (yᶜ : ! Can some y) (zᶜ : ! Can μ z)  → (⟨ a ⟩ · y) · z ≡ ⟨ a ⟩ · (y · z)

data Can {A} where
  εᶜ : Can none ε
  ⟨_⟩ᶜ : ∀ a → Can some ⟨ a ⟩
  ⟨_⟩·ᶜ_ : ∀ a {y : Free A} → Can some y → Can some (⟨ a ⟩ · y)

ε·?_ : ∀ {A μ} {y : Free A} → Can μ y → ε · y ≡ y
ε·? εᶜ = ε·ε
ε·? ⟨ a ⟩ᶜ = ε· ∣ ⟨ a ⟩ᶜ ∣
ε·? (⟨ a ⟩·ᶜ yᶜ) = ε· ∣ ⟨ a ⟩·ᶜ yᶜ ∣

ε·ᶜ_ : ∀ {A μ} {y : Free A} → Can μ y → Can μ (ε · y)
ε·ᶜ_ {A} εᶜ = transport (λ i → Can {A} none (ε·ε (~ i))) εᶜ
ε·ᶜ_ {A} ⟨ a ⟩ᶜ = transport (λ i → Can some ((ε· ∣ ⟨ a ⟩ᶜ ∣) (~ i))) ⟨ a ⟩ᶜ
ε·ᶜ_ {A} {μ} (⟨ a ⟩·ᶜ yᶜ) = transport (λ i → Can μ ((ε· ∣ ⟨ a ⟩·ᶜ yᶜ ∣) (~ i))) (⟨ a ⟩·ᶜ yᶜ) 

_·ᶜε : ∀ {A μ} {x : Free A} → Can μ x → Can μ (x · ε)
_·ᶜε {A} εᶜ = transport (λ i → Can {A} none (ε·ε (~ i))) εᶜ
_·ᶜε {A} {μ} ⟨ a ⟩ᶜ = transport (λ i → Can {A} μ ((∣ ⟨ a ⟩ᶜ ∣ ·ε) (~ i))) ⟨ a ⟩ᶜ
_·ᶜε {A} {μ} (⟨ a ⟩·ᶜ xᶜ) = transport (λ i → Can μ ((∣ ⟨ a ⟩·ᶜ xᶜ ∣ ·ε) (~ i))) (⟨ a ⟩·ᶜ xᶜ)

⟨_⟩·ᶜ?_ : ∀ {A μ} (a : A) {y : Free A} (yᶜ : Can μ y) → Can some (⟨ a ⟩ · y)
⟨_⟩·ᶜ?_ a εᶜ = ⟨ a ⟩ᶜ ·ᶜε
⟨_⟩·ᶜ?_ a ⟨ b ⟩ᶜ = ⟨ a ⟩·ᶜ ⟨ b ⟩ᶜ
⟨_⟩·ᶜ?_ a (⟨ b ⟩·ᶜ yᶜ) = ⟨ a ⟩·ᶜ (⟨ b ⟩·ᶜ yᶜ)

_·ᶜ_ : ∀ {A} {x y : Free A} {μ₁} (xᶜ : Can μ₁ x) {μ₂} (yᶜ : Can μ₂ y) → Can (max μ₁ μ₂) (x · y)
--_·ᶜ_ {μ₁ = .none} εᶜ {μ₂ = none} yᶜ = transport (cong (Can none) ({!!} ∘₃ inv ε·ε ∘₃ cong (_·_ ε) {!!})) yᶜ
_·ᶜ_ {A = A} {μ₁ = .none} εᶜ {μ₂ = none} εᶜ = transport (λ t → Can {A} none (ε·ε (~ t))) εᶜ
_·ᶜ_ {μ₁ = .none} εᶜ {μ₂ = some} yᶜ = transport (λ t → Can some ((ε· ∣ yᶜ ∣) (~ t))) yᶜ
_·ᶜ_ {μ₁ = .some} ⟨ a ⟩ᶜ {μ₂ = none} εᶜ = transport (λ t → Can some ((∣ ⟨ a ⟩ᶜ ∣ ·ε) (~ t))) ⟨ a ⟩ᶜ
_·ᶜ_ {μ₁ = .some} ⟨ a ⟩ᶜ {μ₂ = some} yᶜ = ⟨ a ⟩·ᶜ yᶜ
_·ᶜ_ {μ₁ = .some} (⟨ a ⟩·ᶜ xᶜ) {μ₂ = none} εᶜ = transport (λ t → Can some ((∣ ⟨ a ⟩·ᶜ xᶜ ∣ ·ε) (~ t))) (⟨ a ⟩·ᶜ xᶜ)
_·ᶜ_ {μ₁ = .some} (⟨ a ⟩·ᶜ xᶜ) {μ₂ = some} yᶜ = transport (λ t → Can some ((⟨ a ⟩·₃ ∣ xᶜ ∣ ·₃ ∣ yᶜ ∣) (~ t))) (⟨ a ⟩·ᶜ (xᶜ ·ᶜ yᶜ))

{-
εᶜ ·ᶜ yᶜ = ε·ᶜ yᶜ
⟨ a ⟩ᶜ ·ᶜ yᶜ = ⟨ a ⟩·ᶜ? yᶜ
(⟨ a ⟩·ᶜ xᶜ) ·ᶜ yᶜ = transport (λ i → Can some ((⟨ a ⟩·₃ ∣ xᶜ ∣ ·₃ ∣ yᶜ ∣) (~ i))) (⟨ a ⟩·ᶜ (xᶜ ·ᶜ yᶜ))
-}

count : ∀ {A} → Free A → Count
count ⟨ a ⟩ = some
count ε = none
count (x · y) = max (count x) (count y)
count (ε·ε _) = none
count ((ε·_ {y = y} _) _) = count y
count ((_·ε {x = x} _) i) = max-sym (count x) none i
count ((⟨ a ⟩·₃ yᶜ ·₃ zᶜ) _) = some

{-
lemma : ∀ {A μ} {y : Free A} → (yᶜ : Can μ y) → dpath (λ i → Can μ ((ε·? yᶜ) i)) (ε·ᶜ yᶜ) yᶜ
lemma εᶜ i = {!!}
lemma ⟨ a ⟩ᶜ i = {!!}
lemma (⟨ a ⟩·ᶜ yᶜ) i = {!!}
-}

{-
can! : ∀ {A} (x : Free A) → ! Can (count x) x
can! ⟨ a ⟩ = ∣ ⟨ a ⟩ᶜ ∣
can! ε = ∣ εᶜ ∣
can! (x · y) = ∣ _·ᶜ_ ∣₂ (can! x) (can! y)
can! {A} (ε·ε i) = ∣ transp (λ t → Can {A} none (ε·ε (i ∧ t))) (~ i) (ε·ᶜ εᶜ) ∣
can! (ε·_ {y = y} yᶜ i) = ∣ transp (λ t → Can (count y) ((ε· yᶜ) (t ∧ i))) (~ i) ∣₁ (∣ ε·ᶜ_ ∣₁ (can! y))
can! (_·ε {x = x} xᶜ i) = ∣ transp (λ t → Can (max-sym (count x) none (t ∧ i)) ((xᶜ ·ε) i)) i0 ∣₁ (∣ transp (λ t → Can (max-sym (count x) none (~ t)) ((xᶜ ·ε) i)) i0 ∣₁ (∣ transp (λ t → Can (count x) ((xᶜ ·ε) (t ∧ i))) (~ i) ∣₁ (∣ _·ᶜε ∣₁ (can! x))))
can! (⟨_⟩·₃_·₃_ {y = y} {z = z} a yᶜ zᶜ i) = ∣ transp (λ t → Can some ((⟨ a ⟩·₃ yᶜ ·₃ zᶜ) (t ∧ i))) (~ i) ∣₁ (∣ _·ᶜ_ ∣₂ (∣ _·ᶜ_ ⟨ a ⟩ᶜ ∣₁ (can! y)) (can! z))
-}

can : ∀ {A} (x : Free A) → Can (count x) x
can ⟨ a ⟩ = ⟨ a ⟩ᶜ
can ε = εᶜ
can (x · y) = can x ·ᶜ can y
can {A} (ε·ε i) = transport-path (λ t → Can {A} none (ε·ε (~ t))) εᶜ (~ i)
can {A} ((ε·_ {y = y} yᶜ) i) with count y | can y
can {A} ((ε·_ {y = y} yᶜ) i) | none | yᶜ′ = {!!}
can {A} ((ε·_ {y = y} yᶜ) i) | some | yᶜ′ = {!transp (λ t → Can some ((ε· yᶜ) (t ∧ i))) i0 (ε·ᶜ yᶜ′)!}
can ((xᶜ ·ε) i) = {!!}
can ((⟨ a ⟩·₃ yᶜ ·₃ zᶜ) i) = {!!}

{-
data Free (A : Type) : Type
data Can₁ {A} : Free A → Type

data Free A where
  ⟨_⟩ : A → Free A
  ε : Free A
  _·_ : Free A → Free A → Free A
  ε·ε : ε · ε ≡ ε
  ε·₁_ : ∀ {x} (xᶜ : ! Can₁ x) → ε · x ≡ x
  _·₁ε : ∀ {x} (xᶜ : ! Can₁ x) → x · ε ≡ x
  ⟨_⟩·₃_·₃_ : ∀ {y z} a (yᶜ : ! Can₁ y) (zᶜ : ! Can₁ z) → (⟨ a ⟩ · y) · z ≡ ⟨ a ⟩ · (y · z)

infix 60 _·_ ⟨_⟩·₃_·₃_

pattern ⟨_⟩·₃_·₃_∶_ a y z i = (⟨ a ⟩·₃ y ·₃ z) i

data Can₁ where
  ⟨_⟩ᶜ : ∀ a → Can₁ ⟨ a ⟩
  ⟨_⟩·ᶜ_ : ∀ a {y} → Can₁ y → Can₁ (⟨ a ⟩ · y)

_·ᶜ₁_ : ∀ {A} {x y : Free A} → Can₁ x → Can₁ y → Can₁ (x · y)
⟨ a ⟩ᶜ ·ᶜ₁ yᶜ = ⟨ a ⟩·ᶜ yᶜ
(⟨ a ⟩·ᶜ xᶜ) ·ᶜ₁ yᶜ = transp (λ t → Can₁ (⟨ a ⟩·₃ ∣ xᶜ ∣ ·₃ ∣ yᶜ ∣ ∶ ~ t)) i0 (⟨ a ⟩·ᶜ (xᶜ ·ᶜ₁ yᶜ))

data Can {A} : Free A → Type where
  is-ε : Can ε
  not-ε : ∀ {x} → Can₁ x → Can x

ε·_ : ∀ {A} {x : Free A} → Can x → ε · x ≡ x
ε· is-ε = ε·ε
ε· not-ε xᶜ = ε·₁ ∣ xᶜ ∣

_·ε : ∀ {A} {x : Free A} → Can x → x · ε ≡ x
is-ε ·ε = ε·ε
not-ε xᶜ ·ε = ∣ xᶜ ∣ ·₁ε

_·ᶜ_ : ∀ {A} {x y : Free A} → Can x → Can y → Can (x · y)
is-ε ·ᶜ yᶜ = transport (t ⊢ Can ((ε· yᶜ) (~ t))) yᶜ
xᶜ@(not-ε _) ·ᶜ is-ε = transport (t ⊢ Can ((xᶜ ·ε) (~ t))) xᶜ
not-ε xᶜ ·ᶜ not-ε yᶜ = not-ε (xᶜ ·ᶜ₁ yᶜ)

{-
uncan : ∀ {A} {x : Free A} → Can x → Free A
uncan {x = x} _ = x

uncan₁ : ∀ {A} {x : Free A} → Can₁ x → Free A
uncan₁ {x = x} _ = x
-}

can : ∀ {A} (x : Free A) → Can x
can ⟨ a ⟩ = not-ε ⟨ a ⟩ᶜ
can ε = is-ε
can (x · y) = can x ·ᶜ can y
can {A} (ε·ε i) = transport-path (t ⊢ Can {A} (ε·ε (~ t))) is-ε (~ i)
can ((ε·₁_ {x = x} xᶜ) i) = {!!}
can ((xᶜ ·₁ε) i) = {!!}
can (⟨ a ⟩·₃ xᶜ ·₃ yᶜ ∶ i) = {!!}

to-listᶜ₁ : ∀ {A} {x : Free A} → Can₁ x → List A
to-listᶜ₁ ⟨ a ⟩ᶜ = a ∷ []
to-listᶜ₁ (⟨ a ⟩·ᶜ xᶜ) = a ∷ to-listᶜ₁ xᶜ

to-listᶜ : ∀ {A} {x : Free A} → Can x → List A
to-listᶜ is-ε = []
to-listᶜ (not-ε xᶜ) = to-listᶜ₁ xᶜ

to-list : ∀ {A} → Free A → List A
to-list x = to-listᶜ (can x)

from-list : ∀ {A} → List A → Free A
from-list [] = ε
from-list (a ∷ as) = ⟨ a ⟩ · from-list as
-}
