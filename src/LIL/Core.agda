
-- Low-Level Imperative Language
--  (Syntax only in this module)

--  Design goals:
--      1. Extract trivially to C
--      2. Extract easily to other imperative languages (e.g. JS)

module LIL.Core where

open import Agda.Builtin.String
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool)

-- Types
data Type : Set where
    nat bool : Type

-- Binary operations
data Binop : Type → Type → Type → Set where
    +' ∸' *' /r' %%' : Binop nat nat nat
    =n=' ≤' <' >' ≥' : Binop nat nat bool
    =b=' : Binop bool bool bool
    ∧' ∨' : Binop bool bool bool

-- Embedding literals
⟦_⟧ : Type → Set
⟦ nat ⟧ = Nat
⟦ bool ⟧ = Bool

module PHOAS (Var : Type → Set) where

    -- Expressions & patterns (aka 'L-values' in C)
    data Exp : Type → Set
    data Pat : Type → Set
    
    data Pat where
        var : ∀{t} → Var t → Pat t
        heap[_] : Exp nat → Pat nat
    data Exp where
        # : ∀{t} → ⟦ t ⟧ → Exp t
        _▹_◃_ : ∀{t1 t2 t3} → Exp t1 → Binop t1 t2 t3 → Exp t2 → Exp t3
        ¬ : Exp bool → Exp bool
        !_ : ∀{t} → Pat t → Exp t
        _:=_ : ∀{t} → Pat t → Exp t → Exp t
        _+=_ : Pat nat → Exp nat → Exp nat  -- as in JS, not a pattern
        _∸=_ : Pat nat → Exp nat → Exp nat
        _++ : Pat nat → Exp nat
        _∸∸ : Pat nat → Exp nat

    -- Design Note (Lawrence Jan '23)
    -- Stmt from Expr since...
    --  * Some target languages require an Expr/Stmt split
    --      (e.g. C, which disallows binding on RHS of =)
    --  * It doesn't make a difference for other targets

    data Stmt : Set where
        skip : Stmt
        exp : ∀{t} → Exp t → Stmt
        print : String → ∀{t} → Exp t → Stmt
        while : Exp bool → Stmt → Stmt
        if_then_else_ : Exp bool → Stmt → Stmt → Stmt
        mkvar : ∀ {t} → Exp t → (Var t → Stmt) → Stmt
        _>>_ : Stmt → Stmt → Stmt
