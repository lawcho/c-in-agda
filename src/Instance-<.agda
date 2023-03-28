
open import Data.Nat.Base
open import Function.Base

-- Discover proofs of a ≤ b , a < b when a and b are known
instance 
    z≤n' : ∀{n} → zero ≤ n
    z≤n' = z≤n
    s≤s' : ∀{m n} → {{m ≤ n}} → suc m ≤ suc n
    s≤s' {{pf}} = s≤s pf
