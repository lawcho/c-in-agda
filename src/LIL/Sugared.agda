
-- LIL, but with lots of syntactic sugar added

-- Unlike core LIL, this language is programmer-facing

module LIL.Sugared where

open import Agda.Builtin.String
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Unit using (⊤)
open import Function.Base using (_∘_)

open import LIL.Core using (Type; ⟦_⟧) public
open Type public

-- Kind of terms
data Kindᵗ : Set where exp pat : Kindᵗ

-- Kind of programs
data Kindᵖ : Set where
    stmt : Kindᵖ
    term : Kindᵗ → Type → Kindᵖ

module Variables where variable
    t t1 t2 t3 : Type
    kt kt1 kt2 : Kindᵗ
    kp kp1 kp2 : Kindᵖ
open Variables

module PHOAS (Var : Type → Set) where

    -- LIL programs
    data Prog : Kindᵖ → Set

    Stmt = Prog stmt
    Exp = λ t → Prog (term exp t)
    Pat = λ t → Prog (term pat t)
    Exp' = λ kt t → Prog (term kt t)    -- Exp or Pat

    data Prog where

        var : Var t → Pat t
        heap[_] : Exp' kt nat → Pat nat
        
        # : ⟦ t ⟧ → Exp t
        _+_ _∸_ _*_ _/r_ _%%_ : Exp' kt1 nat → Exp' kt2 nat → Exp nat
        _<_ _>_ _≤_ _≥_ _=n=_ : Exp' kt1 nat → Exp' kt2 nat → Exp bool
        _=b=_ _∧_ _∨_ : Exp' kt1 bool → Exp' kt2 bool → Exp bool
        ¬ : Exp' kt bool → Exp bool

        _+=_ : Pat nat → Exp' kt nat → Exp nat
        _∸=_ : Pat nat → Exp' kt nat → Exp nat
        _++ : Pat nat → Exp nat
        _∸∸ : Pat nat → Exp nat
        _:=_ : Pat t → Exp' kt t → Exp t

        skip : Stmt
        print : String → Exp' kt t → Stmt
        while : Exp' kt bool → Prog kp → Stmt
        if_then_else_ : Exp' kt bool → Prog kp1 → Prog kp2 → Stmt
        mkvar' : Exp' kt t → (Var t → Prog kp) → Stmt
        _>>_ : Prog kp1 → Prog kp2 → Stmt
    infixl 33 _+_ _∸_ _*_ _/r_ _%%_
    infix 32 _<_ _>_ _≤_ _≥_ _=n=_
    infix 31 _=b=_ _∧_ _∨_
    infix 6 _:=_ _+=_ _∸=_ _++ _∸∸
    infix 5 mkvar_
    infixr 4 if_then_else_
    infixr 2 _>>_ _>>=_
    infixl 2 _=<<_

    -- Variant of mkvar' with "var" pre-applied for conciseness
    mkvar_ : Exp' kt t → (Pat t → Prog kp) → Stmt
    mkvar_ e cont = mkvar' e (cont ∘ var)

    _>>=_ : ∀{ℓa ℓb}{A : Set ℓa}{B : A → Set ℓb} → ((a : A) → B a) → (a : A) → B a
    f >>= x = f x

    _=<<_ : ∀{ℓa ℓb}{A : Set ℓa}{B : A → Set ℓb} → (a : A) → ((a : A) → B a) →  B a
    x =<< f = f >>= x

    -- Natural number literal overloading for Prog
    open import Agda.Builtin.FromNat
    instance
        Num-Prog : Number (Prog (term exp nat))
        Num-Prog .Number.Constraint _ = ⊤
        Num-Prog .Number.fromNat n = # n
