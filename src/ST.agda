
-- Adapted from https://gist.github.com/AndrasKovacs/07310be00e2a1bb9e94d7c8dbd1dced6
-- Edits:
--  * Erase postulate (thanks Szumi)
--  * Parametrise out U
--  * Add bind

open import Algebra
open import Data.Bool
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.All
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Reflects

-- Gives a witness to the "truth".
--  Exactly like Relation.Nullary.Decidable.Core.toWitness, but erased
toWitness' : ∀{ℓ}{P : Set ℓ} {Q : Dec P} → @0 True Q → P
toWitness' {Q = true  because [p]} _  = invert [p]
toWitness' {Q = false because  _ } ()

-- Library for ST monad
-----------------------------------------------------------------------------------

module ST-Lib
  (U : Set) (⟦_⟧ : U → Set) -- types that can go into a STRef
  (_U≟_ : (A B : U) → Dec (A ≡ B))  -- used to bypass parametricity postulate
  where

  -- Heap is a heterogeneous list of values in U
  --------------------------------------------------------------------------------

  Heap = All ⟦_⟧

  _[_]≡_ : List U → ℕ → U → Set
  []       [ _     ]≡ b = ⊥
  (a ∷ as) [ zero  ]≡ b = True (a U≟ b)
  (a ∷ as) [ suc n ]≡ b = as [ n ]≡ b

  readHp : ∀ {A As n} → Heap As → @0 As [ n ]≡ A → ⟦ A ⟧
  readHp {As = []}     {n}     hp      ()
  readHp {As = A ∷ As} {zero} (a ∷ hp) p = subst ⟦_⟧ (toWitness' p) a
  readHp {As = A ∷ As} {suc n}(_ ∷ hp) p = readHp hp p

  writeHp : ∀ {A As n} → Heap As → @0 As [ n ]≡ A → ⟦ A ⟧ → Heap As
  writeHp {As = []} {n}         hp       () a
  writeHp {As = A ∷ As} {zero}  (_  ∷ hp) p a = subst ⟦_⟧ (sym (toWitness' p)) a ∷ hp
  writeHp {As = A ∷ As} {suc n} (a' ∷ hp) p a = a' ∷ writeHp hp p a

  pushHp : ∀ {As} → Heap As → ∀ {A} → ⟦ A ⟧ → Heap (As ++ A ∷ [])
  pushHp []        a = a  ∷ []
  pushHp (a' ∷ hp) a = a' ∷ pushHp hp a

  [length] : ∀ as bs b → (as ++ b ∷ bs) [ length as ]≡ b
  [length] []       bs b = fromWitness refl
  [length] (a ∷ as) bs b = [length] as bs b

  --------------------------------------------------------------------------------

  data ST (S : U → Set)(A : Set) : Set where
    ret   : A → ST S A
    new   : ∀ B → ⟦ B ⟧ → (S B → ST S A) → ST S A
    read  : ∀ B → S B → (⟦ B ⟧ → ST S A) → ST S A
    write : ∀ B → S B → ⟦ B ⟧ → ST S A → ST S A

  -- Logical predicate for ST.
  STᴾ : ∀{S}(Sᴾ : ∀ {A} → S A → Set){A}(Aᴾ : A → Set) → ST S A → Set
  STᴾ Sᴾ Aᴾ (ret a)          = Aᴾ a
  STᴾ Sᴾ Aᴾ (new _ _ k)      = ∀ sb → Sᴾ sb → STᴾ Sᴾ Aᴾ (k sb)
  STᴾ Sᴾ Aᴾ (read _ sb k)    = Sᴾ sb × (∀ b → STᴾ Sᴾ Aᴾ (k b))
  STᴾ Sᴾ Aᴾ (write _ sb _ k) = Sᴾ sb × STᴾ Sᴾ Aᴾ k

  -- Concrete ST actions and how to run them
  --------------------------------------------------------------------------------

  ST' : Set → Set
  ST' = ST (λ _ → ℕ)

  Safe : List U → ∀ {A} → ST' A → Set
  Safe As (ret _)         = ⊤
  Safe As (new B _ k)     = Safe (As ++ B ∷ []) (k (length As))
  Safe As (read B n k)    = As [ n ]≡ B × (∀ b → Safe As (k b))
  Safe As (write B n _ k) = As [ n ]≡ B × Safe As k

  runST' : ∀ {A As}(m : ST' A) → @0 Safe As m → Heap As → A
  runST' (ret a)         p       hp = a
  runST' (new _ b k)     p       hp = runST' (k _) p (pushHp hp b)
  runST' (read _ n k)    (p , q) hp = runST' (k _) (q (readHp hp p)) hp
  runST' (write _ n b k) (p , q) hp = runST' k q (writeHp hp p b)

  -- The notion of safety from the free theorem (Safe'+) implies the concrete
  -- notion of safety (Safe)
  --------------------------------------------------------------------------------

  Safe' : List U → ∀ {A} → ST' A → Set
  Safe' As = STᴾ (λ {A} n → As [ n ]≡ A) (λ _ → ⊤)

  Safe'+ : List U → ∀ {A} → ST' A → Set
  Safe'+ As m = ∀ Bs → Safe' (As ++ Bs) m

  Safe'+[] : ∀ {As A m} → Safe'+ As {A} m → Safe' As m
  Safe'+[] {As}{A}{m} safe' = subst (λ x → Safe' x m) (++-identityʳ As) (safe' [])

  Safe'+⇒Safe : ∀ {As A}(m : ST' A) → Safe'+ As m → Safe As m
  Safe'+⇒Safe {As}(ret _) safe'+ = tt

  Safe'+⇒Safe {As}(new B b k) safe'+ =
    Safe'+⇒Safe
      (k (length As))
      (λ Bs → subst
        (λ x → Safe' x (k (length As)))
        (sym (++-assoc As (B ∷ []) Bs))
        (safe'+ (B ∷ Bs) _ ([length] As Bs B)))

  Safe'+⇒Safe {As}(read B n k) safe'+ =
    proj₁ (Safe'+[] {As}{m = read B n k} safe'+) ,
    (λ b → Safe'+⇒Safe (k b) (λ Bs → proj₂ (safe'+ Bs) b))

  Safe'+⇒Safe {As}(write B n b k) safe'+ =
    proj₁ (Safe'+[] {As}{m = write B n b k} safe'+) ,
    Safe'+⇒Safe k (λ Bs → proj₂ (safe'+ Bs))

  --------------------------------------------------------------------------------

  -- The @0 modality proves that the postulate will not block evaluation
  postulate
    @0 free-theorem : ∀ {A}(m : ∀ S → ST S A) → ∀ Aᴾ S (Sᴾ : ∀ {A} → S A → Set) → STᴾ Sᴾ Aᴾ (m S)

  run : ∀ {A} → (∀ S → ST S A) → ST' A
  run m = m (λ _ → ℕ)

  @0 alwaysSafe : ∀ {A As}(m : ∀ S → ST S A) → Safe As (run m)
  alwaysSafe m = Safe'+⇒Safe (run m) (λ Bs → free-theorem m (λ _ → ⊤) _ _)

  runST : ∀ {A} → (∀ S → ST S A) → A
  runST m = runST' (run m) (alwaysSafe m) []

  _=<<_ : ∀{S A B} → (A → ST S B) → ST S A → ST S B
  _=<<_ f (ret a) = f a
  _=<<_ f (new C c k) = new C c (f =<<_ ∘ k)
  _=<<_ f (read C c* k) = read C c* (f =<<_ ∘ k)
  _=<<_ f (write C c c* k) = write C c c* (f =<< k)

  _>>=_ : ∀{S A B} → ST S A → (A → ST S B) → ST S B
  ma >>= f = f =<< ma

--------------------------------------------------------------------------------

-- Examples of using the ST monad
module Examples where


  data U : Set where
    ℕ' Bool' : U
    _⇒_ : U → U → U

  ⟦_⟧ : U → Set
  ⟦ ℕ'    ⟧ = ℕ
  ⟦ Bool' ⟧ = Bool
  ⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

  ⇒-inj : ∀ {A A' B B'} → (A ⇒ B) ≡ (A' ⇒ B') → A ≡ A' × B ≡ B'
  ⇒-inj refl = refl , refl

  _U≟_ : (A B : U) → Dec (A ≡ B)
  ℕ'      U≟ ℕ'        = yes refl
  ℕ'      U≟ Bool'     = no (λ ())
  ℕ'      U≟ (_ ⇒ _)   = no (λ ())
  Bool'   U≟ ℕ'        = no (λ ())
  Bool'   U≟ Bool'     = yes refl
  Bool'   U≟ (_ ⇒ _)   = no (λ ())
  (_ ⇒ _) U≟ ℕ'        = no (λ ())
  (_ ⇒ _) U≟ Bool'     = no (λ ())
  (A ⇒ B) U≟ (A' ⇒ B') with A U≟ A' | B U≟ B'
  ... | yes refl | (yes refl) = yes refl
  ... | yes refl | (no ¬p)    = no (λ p → ¬p (proj₂ (⇒-inj p)))
  ... | no ¬p    | bar        = no (λ p → ¬p (proj₁ (⇒-inj p)))


  open ST-Lib U ⟦_⟧ _U≟_

  ex1 : ∀ S → ST S ℕ
  ex1 S =
    new ℕ' 0 λ x →
    read _ x λ b →
    write _ x (b + 10) $
    read _ x λ b →
    ret b

  computes : runST ex1 ≡ 10
  computes = refl
