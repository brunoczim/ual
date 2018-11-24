module Ual.Either where

infix 10 _∨_
data _∨_ (A B : Set) : Set where
  orL : A → A ∨ B
  orR : B → A ∨ B
