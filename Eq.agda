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

data Equality {a} {A : Set a} ⦃ eqA : Eq A ⦄ : A → A → Set where
  equal    : {x y : A} → x == y → Equality x y
  notEqual : {x y : A} → x ≠ y → Equality x y

record Test {a} (A : Set a) : Set (lsuc a) where
  field
    ⦃ eqA ⦄ : Eq A
    test  : (x : A) → (y : A) → Equality x y
