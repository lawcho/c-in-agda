
-- Core of an extensbile-effects library

-- Implementation based on:

--  "Modular Semantics for Algebraic Effects"
-- https://studenttheses.uu.nl/handle/20.500.12932/37758
-- (I use their 'Sig' construction, to stay in Set₀)
-- (I also use their 'fold' function, to implement generic handlers)

-- "Freer Monads, More Extensible Effects"
--  https://okmij.org/ftp/Haskell/extensible/more.pdf
--  (I use their list-indexed Eff type, to help Agda's unifier)

module Freer.Effect where

open import Function.Base
open import Data.List
open import Data.Fin using (fromℕ<)
open import Data.Nat using (_<_)

-- Type of effect signatures
record Sig : Set₁ where
    constructor _▹_
    field Cmd : Set
    field Res : Cmd → Set
open Sig

-- Non-dependent Sig constructor
_▸_ : Set → Set → Sig
C ▸ R = C ▹ λ _ → R

-- "Algebras over an effect signature"
--  (i.e. 'type of call-like commands')
_-alg_ : Sig → Set → Set
E -alg A = (c : Cmd E) → (Res E c → A) → A

-- Free monad over an effect (aka _⋆_)
data Eff (Ss : List Sig) (A : Set) : Set where
    pure : A → Eff Ss A
    call : ∀ {n} → lookup Ss n -alg (Eff Ss A)

-- General-purpose traversal function over Eff Ss
fold : ∀{A B Ss} → (A → B) → (∀{n} → (lookup Ss n) -alg B) → Eff Ss A → B
fold a→b call' (pure a) = a→b a
fold a→b call' (call c k) = call' c (fold a→b call' ∘ k)

-- Inverse of 'pure'
escape : ∀{A} → Eff [] A → A
escape (pure a) = a

-- A single call and nothing else.
-- (For use in do-blocks)
invoke : ∀{Ss} n → {{p : n < length Ss}}
    → (c : Cmd (lookup Ss (fromℕ< p)))
    → Eff Ss (Res (lookup Ss (fromℕ< p)) c)
invoke n {{pf}} c = call {n = fromℕ< pf} c pure

-- Eff S is a RawMonad
open import Effect.Monad

rawMonad : ∀{Ss} → RawMonad (Eff Ss)
rawMonad = mkRawMonad _ pure λ ea a→eb → fold a→eb call ea

open module M {Ss} = RawMonad (rawMonad {Ss}) public hiding (pure)
