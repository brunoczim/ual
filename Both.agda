module Ual.Both where

infix 10 _∧_
record _∧_ (A B : Set) : Set where
  field
    andL : A
    andR : B
