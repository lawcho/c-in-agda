
-- Interpreter for LIL

module LIL.Interpreter where

open import LIL.Core
open import Instance-<

import Data.Nat as ℕ
import Data.Nat.Show as ℕ
import Data.Nat.Properties as ℕ
import Data.Unit as 𝕋
import Data.Bool as 𝔹
import Data.Bool.Show as 𝔹
import Data.String as 𝕊

open import Function

open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; lookup; updateAt; _∷_; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using (does; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)

pattern here! = here refl

-- Heper for printing values
print-val : ∀{t} → ⟦ t ⟧ → 𝕊.String
print-val {nat}  = ℕ.show
print-val {bool} = 𝔹.show

-- Helper for n-ary function composition
_^_ : ∀{ℓa}{A : Set ℓa} → (A → A) → ℕ.ℕ → A → A
f ^ ℕ.zero = id
f ^ ℕ.suc n = f ∘ f ^ n

-- Lookup in list with default
get-with-default : ∀{ℓa}{A : Set ℓa} → A → ℕ.ℕ → List A → A
get-with-default a _ [] = a
get-with-default _ ℕ.zero (x ∷ _) = x
get-with-default a (ℕ.suc n) (_ ∷ l) = get-with-default a n l

-- Set in list, padding with default value as needed
set-with-default : ∀{ℓa}{A : Set ℓa} → A → A → ℕ.ℕ → List A → List A
set-with-default _ a ℕ.zero (_ ∷ l) = a ∷ l
set-with-default _ a ℕ.zero [] = a ∷ []
set-with-default d a (ℕ.suc n) (x ∷ l) = x ∷ set-with-default d a n l
set-with-default d a (ℕ.suc n) [] = d ∷ set-with-default d a n []

eval-bo : ∀{t1 t2 t3} → Binop t1 t2 t3 → ⟦ t1 ⟧ → ⟦ t2 ⟧ → ⟦ t3 ⟧
eval-bo +' = ℕ._+_
eval-bo ∸' = ℕ._∸_
eval-bo *' = ℕ._*_
eval-bo =n=' = (does ∘_) ∘ ℕ._≟_
eval-bo ≤' = (does ∘_) ∘ ℕ._≤?_
eval-bo <' = (does ∘_) ∘ ℕ._<?_
eval-bo >' = (does ∘_) ∘ ℕ._>?_
eval-bo ≥' = (does ∘_) ∘ ℕ._≥?_
eval-bo =b=' = (does ∘_) ∘ 𝔹._≟_
eval-bo ∧' = 𝔹._∧_
eval-bo ∨' = 𝔹._∨_
-- floor-to-multiple-of
eval-bo /r' m ℕ.zero = ℕ.zero
eval-bo /r' m (ℕ.suc n) = m ℕ./ (ℕ.suc n)
-- offset-from-multiple-of
eval-bo %%' m ℕ.zero    = m
eval-bo %%' m (ℕ.suc n) = m ℕ.% ℕ.suc n

-- Decidable equality for types
dec-≡-Type : DecidableEquality Type
dec-≡-Type nat nat = yes refl
dec-≡-Type bool bool = yes refl
dec-≡-Type nat bool = no λ ()
dec-≡-Type bool nat = no λ ()

open import Freer.Effect
open import Freer.Effect.Writer (𝕊.String) as Writer
open import Freer.Effect.State (List ℕ.ℕ) as State
open import Freer.Effect.MRef Type ⟦_⟧ dec-≡-Type as MRef

-- State thread parameter, for eventual execution
module _ {R : Type → Set} where

    open PHOAS R hiding (_>>_)
    open import Data.Fin using (suc; zero)

    -- Evaluator monad
    M : Set → Set
    M = Eff (Writer.Effect ∷ State.Effect ∷ MRef.Effect R ∷ [])


    -- Read from a pattern
    pat-read : ∀{t} → Pat t → M ⟦ t ⟧

    -- Write to a pattern (and return the written value)
    pat-write : ∀{t} → Pat t → ⟦ t ⟧ → M ⟦ t ⟧

    -- Evaluate an expression
    eval : ∀{t} → Exp t → M ⟦ t ⟧
    eval (# x) = pure x
    eval (¬ e) = 𝔹.not <$> eval e
    eval (e₁ ▹ op ◃ e₂) = eval-bo op <$> eval e₁ <*> eval e₂
    eval (! p) = pat-read p
    eval (p := e) = pat-write p =<< eval e
    eval (p += e) = pat-write p =<< ⦇ (eval-bo +') (pat-read p) (eval e) ⦈
    eval (p ∸= e) = pat-write p =<< ⦇ (eval-bo ∸') (pat-read p) (eval e) ⦈
    eval (p ++)   = pat-write p =<< ⦇ (eval-bo +') (pat-read p) (pure 1) ⦈
    eval (p ∸∸)   = pat-write p =<< ⦇ (eval-bo ∸') (pat-read p) (pure 1) ⦈

    pat-read (var v) = invoke 2 (read v)
    pat-read heap[ e ] = do
        addr ← eval e
        hp ← invoke 1 read
        pure (get-with-default 0 addr hp)

    pat-write (var x) v = invoke 2 (write x v) >> pure v
    pat-write heap[ e ] v = do
        addr ← eval e
        hp ← invoke 1 read
        invoke 1 $ write $ set-with-default 0 v addr hp
        pure v

    -- Evalaute a statement by one step
    step : Stmt → M Stmt
    step (exp e) = eval e >> pure skip
    step skip = pure skip
    step (print s e) = do
        v ← eval e
        invoke 0 (s 𝕊.++ print-val v)
        pure skip
    step (while e s) = pure $ if e then s Stmt.>> while e s else skip
    step (if e then s₁ else s₂) = do
        b ← eval e
        𝔹.if b then step s₁ else step s₂
    step (s₁ Stmt.>> s₂) = do
        skip ← step s₁
            where s₁ → pure $ s₁ Stmt.>> s₂
        step s₂
    step (mkvar e vt→s) = do
        val ← eval e
        vr ← invoke 2 (new val)
        step (vt→s vr)

    -- Run the statement interpreter for n steps
    steps : ℕ.ℕ → Stmt → M Stmt
    steps n s = ((_>=> step) ^ n) pure s

open import Data.Product using (_×_; _,_)
open PHOAS hiding (_>>_)

-- Run the statement interpreter for n steps, with given starting heap
exec' : ℕ.ℕ → List ℕ.ℕ → (∀ R → Stmt R) → (𝕋.⊤ × List 𝕊.String) × List ℕ.ℕ
exec' n hp stmt = run-ST λ R →
    flip State.run hp $ Writer.run $ (steps n (stmt R) >> pure 𝕋.tt) 

-- De-sugar and exec'
open import LIL.Sugared as S
open import LIL.Desugarer
exec : ℕ.ℕ → List ℕ.ℕ → (∀ R → S.PHOAS.Stmt R) → (𝕋.⊤ × List 𝕊.String) × List ℕ.ℕ
exec n l s = exec' n l (de-Stmt ∘ s)
