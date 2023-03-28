
-- Mutable reference effect
-- based on the ST monad

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

module Freer.Effect.MRef
  (U : Set) (⟦_⟧ : U → Set) -- types that can go into references
  (_U≟_ : (A B : U) → Dec (A ≡ B))  -- used to bypass parametricity postulate
  where

open import Freer.Effect

open import ST
open ST-Lib U ⟦_⟧ _U≟_

open import Data.Unit
open import Data.List
open import Data.Fin hiding (fold)
open import Function.Base

module _ (Ref : U → Set) where

  data Cmd : Set where
    read : {u : U} → Ref u → Cmd
    write : {u : U} → Ref u → ⟦ u ⟧ → Cmd
    new : {u : U} → ⟦ u ⟧ → Cmd

  Effect = Cmd ▹ λ where
    (read {u} _) → ⟦ u ⟧
    (write {u} _ _) → ⊤
    (new {u} _) → Ref u

  -- Eliminate an MRef effect (when it is the only effect on the stack).
  un-Eff : ∀{A} → Eff (Effect ∷ []) A → ST Ref A
  un-Eff (pure a) = ret a
  un-Eff (call {zero} (read x) k) = ST.read _ x (un-Eff ∘ k)
  un-Eff (call {zero} (write x y) k) = ST.write _ x y (un-Eff $ k tt)
  un-Eff (call {zero} (new x) k) = ST.new _ x (un-Eff ∘ k) 

-- Wrapper around runST
run-ST : ∀{A} → (∀ R → Eff (Effect R ∷ []) A) → A
run-ST f = runST $ un-Eff _ ∘ f
