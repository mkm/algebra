{-# OPTIONS --cubical #-}
module Arrows where

open import Prelude hiding (!)
open import Data.Fin
open import Data.Vec
open import Data.Tuple

data Arrow : Type where
  [_] : Arrow → Arrow
  com : ℕ → Arrow → Arrow → Arrow
  𝒰 : Arrow
  tuple : ∀ {n} → Vec Arrow n → Arrow
  proj : ∀ n → Fin n → Arrow
  prod : ℕ → Arrow
  case : ∀ {n} → Vec Arrow n → Arrow
  inj : ∀ n → Fin n → Arrow
  sum : ℕ → Arrow
  fix : Arrow → Arrow
  fold : Arrow
  unfold : Arrow
  rec : Arrow → Arrow

infix 50 _·_ _··_ _···_
_·_ _··_ _···_ : Arrow → Arrow → Arrow
_·_ = com 0
_··_ = com 1
_···_ = com 2

! : Arrow
! = tuple []

* : Arrow
* = ! · prod 0

mkprod : ∀ {n} → Vec Arrow n → Arrow
mkprod {n = n} αs = tuple αs · prod n

mkprod₂ : Arrow → Arrow → Arrow
mkprod₂ α β = mkprod (α ∷ β ∷ [])

mksum : ∀ {n} → Vec Arrow n → Arrow
mksum {n = n} αs = tuple αs · sum n

mksum₂ : Arrow → Arrow → Arrow
mksum₂ α β = mksum (α ∷ β ∷ [])

infix 10 _∶_⇒_ _∶_⇒⁺_
data _∶_⇒_ : Arrow → Arrow → Arrow → Type
data _∶_⇒⁺_ : ∀ {n} → Vec Arrow n → Vec Arrow n → Vec Arrow n → Type

record wf (x : Arrow) : Type
data wf⁺ : ∀ {n} → Vec Arrow n → Type

infix 50 _·ₜ_
data _∶_⇒_ where
  t-[] : ∀ {α}
    → wf α
    → [ α ] ∶ α ⇒ α
  t-com₀ : ∀ {α β γ x y}
    → x ∶ α ⇒ β
    → y ∶ β ⇒ γ
    → com 0 x y ∶ α ⇒ γ
  t-comₛ : ∀ h {α β p q r s x y}
    → com h p r ∶ α ⇒ β
    → com h q s ∶ α ⇒ β
    → x ∶ p ⇒ q
    → y ∶ r ⇒ s
    → com (succ h) x y ∶ com h p r ⇒ com h q s
  t-𝒰 : 𝒰 ∶ * ⇒ 𝒰
  t-* : * ∶ * ⇒ 𝒰
  t-tuple : ∀ {α} n {βs xs : Vec Arrow n}
    → wf α
    → xs ∶ replicate n α ⇒⁺ βs
    → tuple xs ∶ α ⇒ mkprod βs
  t-proj : ∀ n {αs : Vec Arrow n} (k : Fin n)
    → wf⁺ αs
    → proj n k ∶ mkprod αs ⇒ αs !! k
  t-prod : ∀ n
    → prod n ∶ mkprod (replicate n 𝒰) ⇒ 𝒰
  t-case : ∀ n {αs xs : Vec Arrow n} {β}
    → xs ∶ αs ⇒⁺ replicate n β
    → case xs ∶ mksum αs ⇒ β
  t-inj : ∀ n {αs : Vec Arrow n} (k : Fin n)
    → inj n k ∶ mksum (replicate n 𝒰) ⇒ 𝒰
  t-sum : ∀ n
    → sum n ∶ mkprod (replicate n 𝒰) ⇒ 𝒰
  t-fix : ∀ {α t}
    → t ∶ mkprod₂ α 𝒰 ⇒ 𝒰
    → fix t ∶ α ⇒ 𝒰
  t-fold : ∀ {α t}
    → fold ∶ tuple ([ α ] ∷ t ∷ []) · fix t ⇒ fix t
  t-unfold : ∀ {α t}
    → unfold ∶ fix t ⇒ tuple ([ α ] ∷ t ∷ []) · fix t
  t-rec : ∀ {β t x}
    → x ∶ β · t ⇒ β
    → rec x ∶ fix t ⇒ β

data _∶_⇒⁺_ where
  ts-[] :
    [] ∶ [] ⇒⁺ []
  ts-∷ : ∀ {x α β n} {xs αs βs : Vec Arrow n}
    → x ∶ α ⇒ β
    → xs ∶ αs ⇒⁺ βs
    → x ∷ xs ∶ α ∷ αs ⇒⁺ β ∷ βs

record wf x where
  constructor mk-wf
  inductive
  field
    {dom} : Arrow
    {cod} : Arrow
    deriv : x ∶ dom ⇒ cod

data wf⁺ where
  wf-[] : wf⁺ []
  wf-∷ : ∀ {n x} {xs : Vec Arrow n}
    → wf x
    → wf⁺ xs
    → wf⁺ (x ∷ xs)

infix 8 _⇒_
record _⇒_ (α β : Arrow) : Type where
  field
    arr : Arrow
    deriv : arr ∶ α ⇒ β

open _⇒_

infix 8 _⇒ₐ_
record _⇒ₐ_ {α β} (p q : α ⇒ β) : Type where
  field
    arrₐ : Arrow
    derivₐ : arrₐ ∶ arr p ⇒ arr q

open _⇒ₐ_

[_]ₐ : ∀ {𝒶 𝒷} → (α : 𝒶 ⇒ 𝒷) → arr α ⇒ arr α
arr [ α ]ₐ = [ arr α ]
deriv [ α ]ₐ = t-[] (mk-wf (deriv α))

_·ₐ_ : ∀ {α β γ} → α ⇒ β → β ⇒ γ → α ⇒ γ
arr (x ·ₐ y) = com 0 (arr x) (arr y)
deriv (x ·ₐ y) = t-com₀ (deriv x) (deriv y)

_··ₐ_ : ∀ {α β γ} {p q : α ⇒ β} {r s : β ⇒ γ} → p ⇒ₐ q → r ⇒ₐ s → p ·ₐ r ⇒ₐ q ·ₐ s
arrₐ (x ··ₐ y) = com 1 (arrₐ x) (arrₐ y)
derivₐ (_··ₐ_ {p = p} {q = q} {r = r} {s = s} x y) = t-comₛ 0 (deriv (p ·ₐ r)) (deriv (q ·ₐ s)) (derivₐ x) (derivₐ y)

𝒰ₐ : * ⇒ 𝒰
arr 𝒰ₐ = 𝒰
deriv 𝒰ₐ = t-𝒰

*ₐ : * ⇒ 𝒰
arr *ₐ = *
deriv *ₐ = t-*

_·ₜ_ : ∀ {α β γ x y} → x ∶ α ⇒ β → y ∶ β ⇒ γ → x · y ∶ α ⇒ γ
_·ₜ_ = t-com₀

t-! : ∀ {α} → wf α → ! ∶ α ⇒ mkprod []
t-! 𝒲 = t-tuple 0 {!!} ts-[]

wf-* : wf *
wf.dom wf-* = *
wf.cod wf-* = 𝒰
wf.deriv wf-* = t-*

t-dom : ∀ {α β x} → x ∶ α ⇒ β → wf α
t-cod : ∀ {α β x} → x ∶ α ⇒ β → wf β

t-dom (t-[] 𝒲) = 𝒲
t-dom (t-com₀ 𝒯x 𝒯y) = t-dom 𝒯x
t-dom (t-comₛ h 𝒯 𝒯₁ 𝒯₂ 𝒯₃) = {!!}
t-dom t-𝒰 = wf-*
t-dom t-* = wf-*
t-dom (t-tuple n 𝒲 xs) = 𝒲
t-dom (t-proj n k 𝒲) = {!!}
t-dom (t-prod n) = {!!}
t-dom (t-case n x) = {!!}
t-dom (t-inj n k) = {!!}
t-dom (t-sum n) = {!!}
t-dom (t-fix 𝒯) = {!!}
t-dom t-fold = {!!}
t-dom t-unfold = {!!}
t-dom (t-rec 𝒯) = {!!}

t-cod 𝒯 = {!!}

t-com₁ : ∀ {α β γ p q r s x y}
  → p ∶ α ⇒ β → q ∶ α ⇒ β → r ∶ β ⇒ γ → s ∶ β ⇒ γ
  → x ∶ p ⇒ q → y ∶ r ⇒ s
  → x ·· y ∶ p · r ⇒ q · s
t-com₁ 𝒯p 𝒯q 𝒯r 𝒯s = t-comₛ 0 (t-com₀ 𝒯p 𝒯r) (t-com₀ 𝒯q 𝒯s)

t-com₂ : ∀ {𝒶 𝒷 𝒸 α β γ δ p q r s x y}
  → α ∶ 𝒶 ⇒ 𝒷 → β ∶ 𝒶 ⇒ 𝒷 → γ ∶ 𝒷 ⇒ 𝒸 → δ ∶ 𝒷 ⇒ 𝒸
  → p ∶ α ⇒ β → q ∶ α ⇒ β → r ∶ γ ⇒ δ → s ∶ γ ⇒ δ
  → x ∶ p ⇒ q → y ∶ r ⇒ s
  → x ··· y ∶ p ·· r ⇒ q ·· s
t-com₂ 𝒯α 𝒯β 𝒯γ 𝒯δ 𝒯p 𝒯q 𝒯r 𝒯s = t-comₛ 1 (t-com₁ 𝒯α 𝒯β 𝒯γ 𝒯δ 𝒯p 𝒯r) (t-com₁ 𝒯α 𝒯β 𝒯γ 𝒯δ 𝒯q 𝒯s)

‵fst : Arrow
‵fst = proj 2 (fin 0)

‵snd : Arrow
‵snd = proj 2 (fin 1)

‵ℕ : Arrow
‵ℕ = fix $ mksum₂ (‵fst · prod 0) ‵snd 

t-‵ℕ : ‵ℕ ∶ * ⇒ 𝒰
t-‵ℕ = t-fix $ t-tuple 2 {!!} (ts-∷ (t-proj 2 (fin 0) {!!} ·ₜ t-prod 0 ) (ts-∷ (t-proj 2 (fin 1) {!!}) ts-[])) ·ₜ t-sum 2

swap : Arrow
swap = tuple (‵snd ∷ ‵fst ∷ [])

t-swap : ∀ {α β} → swap ∶ mkprod (α ∷ β ∷ []) ⇒ mkprod (β ∷ α ∷ [])
t-swap = t-tuple 2 {!!} (ts-∷ (t-proj 2 (fin 1) {!!}) (ts-∷ (t-proj 2 (fin 0) {!!}) ts-[]))

？ : Arrow
？ = case []

t-？ : ∀ {α} → ？ ∶ mksum [] ⇒ α
t-？ = t-case 0 ts-[]
