module Ual.Ord where

open import Agda.Primitive
open import Ual.Void
open import Ual.Eq hiding (sym; trans; self)
open import Ual.Either
open import Ual.Both

record Ord {a} (A : Set a) : Set (lsuc a) where
  infix 30 _<_
  infix 30 _>_
  infix 30 _≤_
  infix 30 _≥_
  field
    ⦃ eq ⦄     : Eq A
    _<_        : A → A → Set
  _>_ : A → A → Set
  x > y = x ≠ y ∧ ¬ (x < y)
  _≤_ : A → A → Set
  x ≤ y = x == y ∨ x < y
  _≥_ : A → A → Set
  x ≥ y = x == y ∨ ¬ (x < y)
  data Order : A → A → Set where
    less    : {x y : A} → x < y → Order x y
    equal   : {x y : A} → x == y → Order x y
    greater : {x y : A} → x > y → Order x y
  field
    compare    : (x : A) → (y : A) → Order x y
    symLess    : {x y : A} → x < y → y ≥ x
    symGreater : {x y : A} → x > y → y ≤ x
    trans      : {x y z : A} → x < y → y < z → x < z

open Ord ⦃ ... ⦄ public

record Compare {a} (A : Set a) : Set (lsuc a) where
  field
    ⦃ ordA ⦄ : Ord A
    compare  : (x : A) → (y : A) → Order x y
