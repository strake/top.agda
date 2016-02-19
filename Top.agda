module Top where

open import Agda.Primitive using (lzero; lsuc)
open import Data.Empty
open import Data.Fin
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function using (_∘_; flip)
import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

record Top {ℓ ℓ₁ ℓ₂ : _} (A : Set ℓ) : Set (ℓ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc ℓ₂) where
    field opens : Pred (Pred A ℓ₁) ℓ₂
          empty : ∃ λ ∅ → Empty     ∅ × ∅ ∈ opens
          full  : ∃ λ U → Universal U × U ∈ opens
          union : (I : Set ℓ₁) → (a : (i : I) → ∃ (flip _∈_ opens)) → ⋃ I (proj₁ ∘ a) ∈ opens
          intersection : (a b : Pred A _) → a ∈ opens → b ∈ opens → a ∩ b ∈ opens
