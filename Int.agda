{-# OPTIONS --cubical --prop --allow-unsolved-metas #-}
module Int where

open import Path
open import Cubical.Foundations.Isomorphism
open import Logic
open import Decidable
open import Nat using (ℕ; ℕ-set)
import Nat as N
open import String
open import Show

data ℤ : Set where
  pos : ℕ → ℤ
  neg : ℕ → ℤ
  zero : pos 0 ≡ neg 0

from-pos : ℤ → ℕ
from-pos (pos n) = n
from-pos (neg _) = 0
from-pos (zero _) = 0

from-neg : ℤ → ℕ
from-neg (pos _) = 0
from-neg (neg n) = n
from-neg (zero _) = 0

pos-inj : ∀ {a b} → pos a ≡ pos b → a ≡ b
pos-inj p i = from-pos (p i)

neg-inj : ∀ {a b} → neg a ≡ neg b → a ≡ b
neg-inj p i = from-neg (p i)

is-sneg : ℤ → Prop
is-sneg (pos _) = ⊥
is-sneg (neg ℕ.zero) = ⊥
is-sneg (neg (ℕ.succ _)) = ⊤
is-sneg (zero _) = ⊥

is-spos : ℤ → Prop
is-spos (pos ℕ.zero) = ⊥
is-spos (pos (ℕ.succ _)) = ⊤
is-spos (neg _) = ⊥
is-spos (zero _) = ⊥

pos≢sneg : ∀ {a b} → pos a ≢ neg (ℕ.succ b)
pos≢sneg p = proof (transp (λ t → ♯ (is-sneg (p (~ t)))) i0 (lift top))

spos≢neg : ∀ {a b} → pos (ℕ.succ a) ≢ neg b
spos≢neg p = proof (transp (λ t → ♯ (is-spos (p t))) i0 (lift top))

trisect : {A : Set} → (ℕ → A) → A → (ℕ → A) → ℤ → A
trisect f-pos f-zero f-neg (pos ℕ.zero) = f-zero
trisect f-pos f-zero f-neg (pos (ℕ.succ n)) = f-pos n
trisect f-pos f-zero f-neg (neg ℕ.zero) = f-zero
trisect f-pos f-zero f-neg (neg (ℕ.succ n)) = f-neg n
trisect f-pos f-zero f-neg (zero _) = f-zero

trisect-ind : {A : ℤ → Set} → ((n : ℕ) → A (pos (ℕ.succ n))) → A (pos 0) → ((n : ℕ) → A (neg (ℕ.succ n))) → (n : ℤ) → A n
trisect-ind f-pos f-zero f-neg (pos ℕ.zero) = f-zero
trisect-ind f-pos f-zero f-neg (pos (ℕ.succ n)) = f-pos n
trisect-ind {A} f-pos f-zero f-neg (neg ℕ.zero) = transp (λ t → A (zero t)) i0 f-zero
trisect-ind f-pos f-zero f-neg (neg (ℕ.succ n)) = f-neg n
trisect-ind {A} f-pos f-zero f-neg (zero i) = transp (λ t → A (zero (t ∧ i))) (~ i) f-zero

syntax trisect-ind (λ m → f-pos) f-zero (λ n → f-neg) = pos⟨ m ⟩∶ f-pos zero∶ f-zero neg⟨ n ⟩∶ f-neg

bisect-into-prop : {A : ℤ → Set} → (∀ n → is-prop (A n)) → ((n : ℕ) → A (pos n)) → ((n : ℕ) → A (neg n)) → (n : ℤ) → A n
bisect-into-prop A-prop f-pos f-neg (pos n) = f-pos n
bisect-into-prop A-prop f-pos f-neg (neg n) = f-neg n
bisect-into-prop A-prop f-pos f-neg (zero i) = prop-is-dprop (λ i → A-prop (zero i)) (f-pos 0) (f-neg 0) i

syntax bisect-into-prop A-prop (λ m → f-pos) (λ n → f-neg) = into-prop A-prop pos⟨ m ⟩∶ f-pos neg⟨ n ⟩∶ f-neg

bisect-into-prop₂ : {A : ℤ → ℤ → Set} → (∀ m n → is-prop (A m n)) → ((m n : ℕ) → A (pos m) (pos n)) → ((m n : ℕ) → A (pos m) (neg n)) → ((m n : ℕ) → A (neg m) (pos n)) → ((m n : ℕ) → A (neg m) (neg n)) → (m n : ℤ) → A m n
bisect-into-prop₂ A-prop f-pos-pos f-pos-neg f-neg-pos f-neg-neg = into-prop (λ m p q i n → A-prop m n (p n) (q n) i)
  pos⟨ m ⟩∶ into-prop (λ n → A-prop (pos m) n)
    pos⟨ n ⟩∶ f-pos-pos m n
    neg⟨ n ⟩∶ f-pos-neg m n
  neg⟨ m ⟩∶ into-prop (λ n → A-prop (neg m) n)
    pos⟨ n ⟩∶ f-neg-pos m n
    neg⟨ n ⟩∶ f-neg-neg m n

bisect-into-prop₃ : {A : ℤ → ℤ → ℤ → Set} → (∀ a b c → is-prop (A a b c)) →
  ((a b c : ℕ) → A (pos a) (pos b) (pos c)) →
  ((a b c : ℕ) → A (pos a) (pos b) (neg c)) →
  ((a b c : ℕ) → A (pos a) (neg b) (pos c)) →
  ((a b c : ℕ) → A (pos a) (neg b) (neg c)) →
  ((a b c : ℕ) → A (neg a) (pos b) (pos c)) →
  ((a b c : ℕ) → A (neg a) (pos b) (neg c)) →
  ((a b c : ℕ) → A (neg a) (neg b) (pos c)) →
  ((a b c : ℕ) → A (neg a) (neg b) (neg c)) →
  (a b c : ℤ) → A a b c
bisect-into-prop₃ A-prop f-pos-pos-pos f-pos-pos-neg f-pos-neg-pos f-pos-neg-neg f-neg-pos-pos f-neg-pos-neg f-neg-neg-pos f-neg-neg-neg =
  into-prop (λ a p q i b c → A-prop a b c (p b c) (q b c) i)
    pos⟨ a ⟩∶ bisect-into-prop₂ (λ _ _ → A-prop _ _ _)
      (f-pos-pos-pos a)
      (f-pos-pos-neg a)
      (f-pos-neg-pos a)
      (f-pos-neg-neg a)
    neg⟨ a ⟩∶ bisect-into-prop₂ (λ _ _ → A-prop _ _ _)
      (f-neg-pos-pos a)
      (f-neg-pos-neg a)
      (f-neg-neg-pos a)
      (f-neg-neg-neg a)

dec-eq : (m n : ℤ) → Dec (m ≡ n)
dec-eq =
  pos⟨ m ⟩∶
    pos⟨ n ⟩∶ dec-inj pos pos-inj (dec-inj ℕ.succ N.succ-inj (N.dec-eq m n))
    zero∶ no (λ p → spos≢neg (p ∘ zero))
    neg⟨ n ⟩∶ no (λ p → pos≢sneg p)
  zero∶
    pos⟨ n ⟩∶ no (λ p → N.zero≢succ (pos-inj p))
    zero∶ yes id
    neg⟨ n ⟩∶ no (λ p → N.zero≢succ (neg-inj (zero ~∘ p)))
  neg⟨ m ⟩∶
    pos⟨ n ⟩∶ no (λ p → pos≢sneg (inv p))
    zero∶ no (λ p → pos≢sneg (inv p))
    neg⟨ n ⟩∶ dec-inj neg neg-inj (dec-inj ℕ.succ N.succ-inj (N.dec-eq m n))

ℤ-set : is-set ℤ
ℤ-set = dec-eq-set dec-eq

_∖_ : ℕ → ℕ → ℤ
ℕ.zero ∖ n = neg n
m@(ℕ.succ _) ∖ ℕ.zero = pos m
ℕ.succ m ∖ ℕ.succ n = m ∖ n

infixr 50 _∖_

∖-zero-right : ∀ a → a ∖ 0 ≡ pos a
∖-zero-right ℕ.zero i = zero (~ i)
∖-zero-right (ℕ.succ a) i = pos (ℕ.succ a)

∖-same : ∀ a → a ∖ a ≡ pos 0
∖-same ℕ.zero = inv zero
∖-same (ℕ.succ a) = ∖-same a

succ : ℤ → ℤ
succ (pos n) = pos (ℕ.succ n)
succ (neg ℕ.zero) = pos 1
succ (neg (ℕ.succ n)) = neg n
succ (zero _) = pos 1

pred : ℤ → ℤ
pred (pos ℕ.zero) = neg 1
pred (pos (ℕ.succ n)) = pos n
pred (neg n) = neg (ℕ.succ n)
pred (zero _) = neg 1

succ-pred : ∀ a → succ (pred a) ≡ a
succ-pred (pos ℕ.zero) i = zero (~ i)
succ-pred (pos (ℕ.succ a)) _ = pos (ℕ.succ a)
succ-pred (neg a) _ = neg a
succ-pred (zero i) j = zero (i ∨ ~ j)

pred-succ : ∀ a → pred (succ a) ≡ a
pred-succ (pos a) _ = pos a
pred-succ (neg ℕ.zero) i = zero i
pred-succ (neg (ℕ.succ a)) _ = neg (ℕ.succ a)
pred-succ (zero i) j = zero (i ∧ j)

∖-succ-left : ∀ a b → ℕ.succ a ∖ b ≡ succ (a ∖ b)
∖-succ-left ℕ.zero ℕ.zero _ = pos 1
∖-succ-left ℕ.zero (ℕ.succ b) _ = neg b
∖-succ-left (ℕ.succ a) ℕ.zero _ = pos (ℕ.succ (ℕ.succ a))
∖-succ-left (ℕ.succ a) (ℕ.succ b) = ∖-succ-left a b

_+_ : ℤ → ℤ → ℤ
pos m + pos n = pos (m N.+ n)
pos m + neg n = m ∖ n
pos m + zero j = ((λ i → pos (N.+-zero-right m i)) ∘~ ∖-zero-right m) j
neg m + pos n = n ∖ m
neg m + neg n = neg (m N.+ n)
neg m + zero j = neg (N.+-zero-right m (~ j))
zero i + pos n = ∖-zero-right n (~ i)
zero i + neg n = neg n
zero i + zero j =
  hcomp (λ h → λ { (i = i0) → ∘-id-left zero (~ h) j
                 ; (i = i1) → neg 0
                 ; (j = i0) → zero i
                 ; (j = i1) → neg 0 }) (zero (i ∨ j))

infixr 50 _+_

+-zero-left : (a : ℤ) → pos 0 + a ≡ a
+-zero-left (pos a) _ = pos a
+-zero-left (neg a) _ = neg a
+-zero-left (zero i) j = ∘-id-left zero j i

+-zero-right : (a : ℤ) → a + pos 0 ≡ a
+-zero-right (pos a) i = pos (N.+-zero-right a i)
+-zero-right (neg a) _ = neg a
+-zero-right (zero i) _ = zero i

+-succ-left : (a b : ℤ) → succ a + b ≡ succ (a + b)
+-succ-left (pos a) (pos b) _ = pos (ℕ.succ (a N.+ b))
+-succ-left (pos a) (neg b) = ∖-succ-left a b
+-succ-left (pos a) (zero j) = {!!}
+-succ-left (neg a) b = {!!}
+-succ-left (zero i) b = {!!}

+-comm : (a b : ℤ) → a + b ≡ b + a
+-comm = bisect-into-prop₂ (λ _ _ → ℤ-set _ _)
  (λ a b i → pos (N.+-comm a b i))
  (λ a b → id)
  (λ a b → id)
  (λ a b i → neg (N.+-comm a b i))

∖-+-left : ∀ a b c → (a N.+ b) ∖ c ≡ pos a + b ∖ c
∖-+-left ℕ.zero b c i = +-zero-left (b ∖ c) (~ i)
∖-+-left (ℕ.succ a) b c = {!!}

+-assoc : (a b c : ℤ) → (a + b) + c ≡ a + (b + c)
+-assoc = bisect-into-prop₃ (λ _ _ _ → ℤ-set _ _)
  (λ a b c i → pos (N.+-assoc a b c i))
  (λ a b c → {!!})
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  (λ a b c i → neg (N.+-assoc a b c i))
{-
+-assoc (pos a) (pos b) (pos c) ℓ = pos (N.+-assoc a b c ℓ)
+-assoc (pos a) (pos b) (neg c) = {!!}
+-assoc (pos a) (pos b) (zero k) = {!!}
+-assoc (pos a) (neg b) c = {!!}
+-assoc (pos a) (zero j) c = {!!}
+-assoc (neg a) b c = {!!}
+-assoc (zero i) b c = {!!}
-}

_·_ : ℤ → ℤ → ℤ
pos m · pos n = pos (m N.· n)
pos m · neg n = neg (m N.· n)
pos m · zero j =
  hcomp (λ h → λ { (j = i0) → pos (N.·-zero-right m (~ h))
                 ; (j = i1) → neg (N.·-zero-right m (~ h)) }) (zero j)
neg m · pos n = neg (m N.· n)
neg m · neg n = pos (m N.· n)
neg m · zero j =
  hcomp (λ h → λ { (j = i0) → neg (N.·-zero-right m (~ h))
                 ; (j = i1) → pos (N.·-zero-right m (~ h)) }) (zero (~ j))
zero i · pos n = zero i
zero i · neg n = zero (~ i)
zero i · zero j =
  hcomp (λ h → λ { (j = i0) → zero i
                 ; (j = i1) → zero (~ i) }) (zero ((i ∨ j) ∧ (~ i ∨ ~ j)))

infixr 60 _·_

·-comm : (a b : ℤ) → a · b ≡ b · a
·-comm = bisect-into-prop₂ (λ _ _ → ℤ-set _ _)
  (λ a b i → pos (N.·-comm a b i))
  (λ a b i → neg (N.·-comm a b i))
  (λ a b i → neg (N.·-comm a b i))
  λ a b i → pos (N.·-comm a b i)

·-assoc : (a b c : ℤ) → (a · b) · c ≡ a · (b · c)
·-assoc = bisect-into-prop₃ (λ _ _ _ → ℤ-set _ _)
  (λ a b c i → pos (N.·-assoc a b c i))
  (λ a b c i → neg (N.·-assoc a b c i))
  (λ a b c i → neg (N.·-assoc a b c i))
  (λ a b c i → pos (N.·-assoc a b c i))
  (λ a b c i → neg (N.·-assoc a b c i))
  (λ a b c i → pos (N.·-assoc a b c i))
  (λ a b c i → pos (N.·-assoc a b c i))
  (λ a b c i → neg (N.·-assoc a b c i))

-_ : ℤ → ℤ
- pos n = neg n
- neg n = pos n
- zero i = zero (~ i)

infixr 100 -_

neg-involution : (a : ℤ) → - - a ≡ a
neg-involution (pos a) _ = pos a
neg-involution (neg a) _ = neg a
neg-involution (zero i) _ = zero i

+-neg-left : (a : ℤ) → - a + a ≡ pos 0
+-neg-left = into-prop (λ _ → ℤ-set _ _)
  pos⟨ a ⟩∶ ∖-same a
  neg⟨ a ⟩∶ ∖-same a

abs : ℤ → ℕ
abs (pos n) = n
abs (neg n) = n
abs (zero _) = 0

sgn : ℤ → ℤ
sgn (pos n) = pos (N.sgn n)
sgn (neg n) = neg (N.sgn n)
sgn (zero i) = zero i

abs-sgn : ∀ a → sgn a · pos (abs a) ≡ a
abs-sgn (pos ℕ.zero) _ = pos 0
abs-sgn (pos a@(ℕ.succ _)) _ = pos a
abs-sgn (neg ℕ.zero) _ = neg 0
abs-sgn (neg a@(ℕ.succ _)) _ = neg a
abs-sgn (zero i) _ = zero i

iterate-path : {A : Set} {x : A} → ℤ → x ≡ x → x ≡ x
iterate-path (pos n) p = N.iterate-path n p
iterate-path (neg n) p = N.iterate-path n (inv p)
iterate-path (zero _) p = id

succ-path : ℤ ≡ ℤ
succ-path = isoToPath φ
  where
    φ : Iso ℤ ℤ
    Iso.fun φ = succ
    Iso.inv φ = pred
    Iso.rightInv φ = succ-pred
    Iso.leftInv φ = pred-succ

instance
  show-ℤ : Show ℤ
  Show.show show-ℤ (pos ℕ.zero) = "0"
  Show.show show-ℤ (pos n@(ℕ.succ _)) = "+" ⋯ show n
  Show.show show-ℤ (neg ℕ.zero) = "0"
  Show.show show-ℤ (neg n@(ℕ.succ _)) = "-" ⋯ show n
  Show.show show-ℤ (zero i) = "0"
