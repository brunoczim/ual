module Ual.Void where

data ⊥ : Set where

¬ : Set → Set
¬ p = p → ⊥
