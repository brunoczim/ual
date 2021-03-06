module Ual.Ord where

open import Agda.Primitive
open import Ual.Void
open import Ual.Eq
open import Ual.Either
open import Ual.Both

record Ord {a} (A : Set a) : Set (lsuc a) where
  infix 30 _<_
  infix 30 _>_
  infix 30 _≤_
  infix 30 _≥_
  field
    ⦃ eqA ⦄     : Eq A
    _<_        : A → A → Set
  _>_ : A → A → Set
  x > y = x ≠ y ∧ ¬ (x < y)
  _≤_ : A → A → Set
  x ≤ y = x == y ∨ x < y
  _≥_ : A → A → Set
  x ≥ y = x == y ∨ x > y
  field
    ltNotEq : {x y : A} → x < y → x ≠ y
    symLt   : {x y : A} → x < y → y > x
    symGt   : {x y : A} → x > y → y < x
    transLt : {x y z : A} → x < y → y < z → x < z
    transLe : {x y z : A} → x ≤ y → y ≤ z → x ≤ z

  symLe : {x y : A} → x ≤ y → y ≥ x
  symLe (orL eq) = orL (sym ⦃ eqA ⦄ eq)
  symLe (orR lt) = orR (symLt lt)
  symGe : {x y : A} → x ≥ y → y ≤ x
  symGe (orL eq) = orL (sym ⦃ eqA ⦄ eq)
  symGe (orR gt) = orR (symGt gt)

  transGt : {x y z : A} → x > y → y > z → x > z
  transGt gt1 gt2 = symLt (transLt (symGt gt2) (symGt gt1))
  transGe : {x y z : A} → x ≥ y → y ≥ z → x ≥ z
  transGe ge1 ge2 = symLe (transLe (symGe ge2) (symGe ge1))

open Ord ⦃ ... ⦄ public

data Order {a} {A : Set a} ⦃ ordA : Ord A ⦄ : A → A → Set where
  less    : {x y : A} → x < y → Order x y
  equal   : {x y : A} → x == y → Order x y
  greater : {x y : A} → x > y → Order x y

record Compare {a} (A : Set a) : Set (lsuc a) where
  field
    ⦃ ordA ⦄ : Ord A
    compare  : (x : A) → (y : A) → Order x y
