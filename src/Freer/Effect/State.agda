
module Freer.Effect.State (X : Set) where

open import Freer.Effect

open import Data.Product using (_×_; _,_; map₂)
open import Data.Unit
open import Data.Fin hiding (fold)
open import Data.List
open import Function.Base

data Cmd : Set where
    read : Cmd
    write : X → Cmd

-- The signature of state effects
Effect = Cmd ▹ λ where
    read → X
    (write _) → ⊤

-- Eliminate a state effect, taking an initial state producing a final state
run : ∀{A Ss} → Eff (Effect ∷ Ss) A → X → Eff Ss (A × X)
run = fold (λ a x → pure (a , x)) λ where
    {zero} read x→x→ea x → x→x→ea x x
    {zero} (write x) ⊤→x→ea _ → ⊤→x→ea tt x
    {suc n} c rc→x→ea x → call c (flip rc→x→ea x)
