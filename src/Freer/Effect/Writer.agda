
module Freer.Effect.Writer (X : Set) where

open import Freer.Effect
open import Data.Product using (_×_; _,_; map₂)
open import Data.Unit
open import Data.Fin hiding (fold)
open import Data.List

-- The signature of writer effects
Effect = X ▸ ⊤

-- Eliminate a writer effect, producing a list of put values
run : ∀{A Ss} → Eff (Effect ∷ Ss) A → Eff Ss (A × List X)
run = fold (λ a → pure (a , [])) λ where
    {zero} x ⊤→ea → (map₂ (x ∷_)) <$> (⊤→ea tt)
    {suc n} → call
