module Ual.Eq where

open import Agda.Primitive
open import Ual.Void

record Eq {a} (A : Set a) : Set (lsuc a) where
  infix 30 _==_
  infix 30 _≠_
  field
    _==_  : A → A → Set
    self  : {x : A} → x == x
    sym   : {x y : A} → x == y → y == x
    trans : {x y z : A} → x == y → y == z → x == z
  _≠_  : A → A → Set
  x ≠ y = ¬ (x == y)

open Eq ⦃ ... ⦄ public

data Test {a} {A : Set a} ⦃ eqA : Eq A ⦄ : A → A → Set where
  equal    : {x y : A} → x == y → Test x y
  notEqual : {x y : A} → x ≠ y → Test x y
