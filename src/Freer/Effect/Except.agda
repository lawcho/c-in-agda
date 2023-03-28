
-- Exception effect

module Freer.Effect.Except (X : Set) where

open import Freer.Effect

open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List
open import Data.Fin hiding (fold)
open import Function.Base

-- Signature of exception effects
Effect = X ▸ ⊥

-- Eliminate an exception effect, producing an Either value
run : ∀{A Ss} → Eff (Effect ∷ Ss) A → Eff Ss (A ⊎ X)
run = fold (pure ∘ inj₁) λ where
    {zero} x ⊥→ea → pure (inj₂ x)
    {suc n} → call
