
-- Example LIL programs

module LIL.Examples where

open import LIL.Sugared
open import Function.Base

open import Agda.Builtin.Unit
open import Agda.Builtin.FromNat

private variable kt kt1 kt2 kt3 : Kindᵗ

module Programs (Var : Type → Set) where

    open PHOAS Var

    -- multiply by three until the number is greater than 100
    mult3 : Exp nat → Stmt
    mult3 e = do
        x ← mkvar e
        while (x < 100) do
            print "x == " x
            x := x * 3
    
    even : Exp' kt nat → Exp bool
    even n = n %% 2 =n= 0

    -- find the maximum value in heap[lower..upper], and put it in heap[out]
    list-max : Exp' kt1 nat → Exp' kt2 nat → Exp' kt3 nat → Stmt
    list-max lower upper out = do
        lower ← mkvar lower
        upper ← mkvar upper
        max ← mkvar 0
        while (lower ≤ upper) do
            i ← mkvar heap[ lower ]
            if (i ≥ max)
                then max := i
                else skip
            lower ++
        heap[ out ] := max

    -- Swap heap[x] and heap[y]
    swap : Exp' kt1 nat → Exp' kt2 nat → Stmt
    swap x y = do
        tmp ← mkvar heap[ x ]
        heap[ x ] := heap[ y ]
        heap[ y ] := tmp

    -- Reverse heap[lower..upper] in place
    reverse : Exp' kt1 nat → Exp' kt2 nat → Stmt
    reverse l u = do
        l ← mkvar l
        u ← mkvar u
        while (l < u) do
            swap l u
            l ++
            u ∸∸

    -- Selection sort
    sel-sort : Exp' kt1 nat → Exp' kt2 nat → Stmt
    sel-sort base n = do
        i ← mkvar base
        n ← mkvar n
        while (i < n) do
            j ← mkvar i + 1
            while (j < n) do
                if heap[ j ] < heap[ i ]
                    then swap i j
                    else skip
                j ++
            i ++


    -- Union-find example
    set-parent : Exp' kt nat → Exp' kt nat → Exp nat
    set-parent node parent = heap[ node ] := parent

    get-parent : Exp' kt nat → Pat nat
    get-parent a = heap[ a ]

    get-class : Exp' kt nat → Stmt
    get-class a = do
        a ← mkvar a
        top ← mkvar a
        -- search pass
        while (¬ (get-parent top =n= top)) do
            top := get-parent top
        -- update pass
        while (¬ (a =n= top)) do
            next ← mkvar get-parent a
            set-parent a top
            a := next

    unify : Exp' kt1 nat → Exp' kt2 nat → Stmt
    unify a b = do
        get-class a
        get-class b
        a ← mkvar get-parent a
        b ← mkvar get-parent b
        set-parent a b

    demo = do
        unify 0 1
        unify 0 2
        unify 0 3
        unify 0 4

    -- bubble sort
    bubble : Exp' kt nat → Stmt
    bubble n = do
        n ← mkvar n
        i ← mkvar 0
        while (i < n) do
            j ← mkvar i
            while (j < n) do
                if heap[ j ] > heap[ j + 1 ]
                    then swap j (j + 1)
                    else skip
                j ++
            i ++
open import LIL.Interpreter
open import Data.List
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open PHOAS

open import Agda.Builtin.Nat using (Nat)
instance Num-Nat = record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }

cycles = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9
    ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ []

randoms
 = 47 ∷ 11 ∷ 61 ∷ 14 ∷ 19 ∷ 68 ∷ 38 ∷ 21 ∷ 48 ∷ 95 ∷ 43 ∷ 16 ∷ 94 ∷ 33 ∷ 40 ∷ 65 ∷ 42 ∷ 36 ∷ 55 ∷ 46 ∷ 84 ∷ 20 ∷ 15 ∷ 9
 ∷ 51 ∷ 76 ∷ 22 ∷ 83 ∷ 92 ∷ 3 ∷ 54 ∷ 34 ∷ 18 ∷ 56 ∷ 6 ∷ 10 ∷ 78 ∷ 23 ∷ 1 ∷ 97 ∷ 50 ∷ 8 ∷ 60 ∷ 31 ∷ 30 ∷ 4 ∷ 44 ∷ 52 ∷ 13 ∷ 74 ∷ []

-- Examples
ex1 = exec 30 [] λ R → Programs.mult3 R (# 9)

ex2 = λ n → exec 500 (0 ∷ 4 ∷ 2 ∷ 6 ∷ 8 ∷ 5 ∷ 3 ∷ [])
    λ R → Programs.list-max R (# 1) (# n) (# 0)

ex3 = exec 500 (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ [])
    λ R → Programs.reverse R (# 2) (# 6)

ex4 = exec 500 randoms
    λ R → Programs.sel-sort R (# 0) (# 7)

ex5 = exec 500 cycles
    λ R → Programs.demo R

ex6 = exec 500 randoms
    λ R → Programs.bubble R (# 10)
