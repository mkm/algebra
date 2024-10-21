{-# OPTIONS --cubical --prop #-}
module UPair where

open import Cubical.Foundations.Isomorphism
open import Path
open import Logic
open import Truncation
open import Bool
open import Nat

record UPair {ℓ} (A : Type ℓ) : Type (lsuc lzero ⊔ ℓ) where
  field
    Index : Type
    bool : ■₀ (Bool ≡ Index)
    proj : Index → A

open UPair public

select : {A : Type} → A → A → Bool → A
select x y false = x
select x y true = y

lemma : {A : Type} (x y : A) → transport (λ t → not-path t → A) (select x y) ≡ select y x
lemma {A} x y i b = {!transp (λ t → not-path (t ∨ i) → A) i!}

not-select : {A : Type} (x : A) (y : A) → PathP (λ i → not-path i → A) (select x y) (select y x)
not-select {A} x y i b = {!transp (λ t → A → A → not-path t → A) i0 select x y false!} -- {!select x y (prim^unglue {A = Bool} {T = λ { (i = i0) → Bool ; (i = i1) → Bool }} {e = λ { (i = i0) → id-equiv ; (i = i1) → isoToEquiv not-iso }} b)!} -- {!glue {T = λ { (i = i0) → Bool → A ; (i = i1) → Bool → A }} (λ { (i = i0) → select x y ; (i = i1) → select y x }) (Bool → A)!}

upair : ∀ {A} → A → A → UPair A
Index (upair x y) = Bool
bool (upair x y) = forget₀ id
proj (upair x y) = select x y

into-prop : ∀ {ℓ₁} {ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → is-prop B → (A → A → B) → UPair A → B
into-prop pr f x = from-■₀ pr (λ p → f (proj x (transport p false)) (proj x (transport p true))) (bool x)

this : ∀ {ℓ} {A : Type ℓ} → UPair A → ■₀ A
this = into-prop collapse₀ (λ a _ → forget₀ a)

that : ∀ {ℓ} {A : Type ℓ} → UPair A → ■₀ A
that = into-prop collapse₀ (λ _ a → forget₀ a)

comm : ∀ {A} (x y : A) → upair x y ≡ upair y x
Index (comm x y i) = not-path i
bool (comm x y i) = {!forget₀ λ j → not-path (i ∧ j)!} -- ∣ (λ j → not-path (i ∧ j)) ∣
proj (comm {A} x y i) = not-select x y i

record MType : Type₁ where
  eta-equality
  field
    carrier : Type
    inhabitant : carrier
    m-prop : is-prop carrier

open MType

m-type-carrier-iso : (A B : MType) → Iso (carrier A) (carrier B)
Iso.fun (m-type-carrier-iso A B) _ = inhabitant B
Iso.inv (m-type-carrier-iso A B) _ = inhabitant A
Iso.rightInv (m-type-carrier-iso A B) = m-prop B (inhabitant B)
Iso.leftInv (m-type-carrier-iso A B) = m-prop A (inhabitant A)

m-type-carrier-prop : (A B : MType) → carrier A ≡ carrier B
m-type-carrier-prop A B i = iso-path φ i
  where
    φ : Iso (carrier A) (carrier B)
    Iso.fun φ _ = inhabitant B
    Iso.inv φ _ = inhabitant A
    Iso.rightInv φ = m-prop B (inhabitant B)
    Iso.leftInv φ = m-prop A (inhabitant A)

m-type-prop : is-prop MType
MType.carrier (m-type-prop A B i) = iso-path (m-type-carrier-iso A B) i
MType.inhabitant (m-type-prop A B i) = to-iso-path (m-type-carrier-iso A B) (inhabitant A) i
MType.m-prop (m-type-prop A B i) = (prop-is-dprop λ j → is-prop-is-prop (iso-path (m-type-carrier-iso A B) j)) (m-prop A) (m-prop B) i

record Single {ℓ} {A : Type ℓ} (x : A) : Type ℓ where
  field
    elem : A
    single : elem ≡ x

open Single

single-prop : ∀ {ℓ} {A : Type ℓ} (x : A) → is-prop (Single x)
elem (single-prop x a b i) = (single a ∘~ single b) i
single (single-prop x a b i) = {!!}

cadd-type : UPair ℕ → Type
cadd-type x = carrier (into-prop m-type-prop T x)
  where
    T : ℕ → ℕ → MType
    carrier (T m n) = Single (m + n)
    Single.elem (inhabitant (T m n)) = m + n
    Single.single (inhabitant (T m n)) = id
    m-prop (T m n) = single-prop (m + n)

cadd : (x : UPair ℕ) → cadd-type x
cadd x = into-prop {!single-prop _!} {!!} x
