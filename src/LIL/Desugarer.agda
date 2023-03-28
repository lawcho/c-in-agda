
-- De-sugarer from Sugared LIL to Core LIL

module LIL.Desugarer where

open import LIL.Core as Core
open import LIL.Sugared as Sugared

module _ {Var : Type → Set} where

    open module S = Sugared.PHOAS Var
    open module C = Core.PHOAS Var

    -- De-sugar Exp/Pat/Stmt s
    de-Pat : ∀ {t} → S.Pat t → C.Pat t
    de-Exp : ∀ {t} → S.Exp t → C.Exp t
    de-Stmt : S.Stmt → C.Stmt

    -- Varaints that also resolve sub-typing inclusions
    de-Exp⁻ : ∀ {ke t} → S.Exp' ke t → C.Exp t  -- Pat ⊆ Exp
    de-Stmt⁻ : ∀{kp} → S.Prog kp → C.Stmt       -- Exp ⊆ Stmt

    de-Pat (var x) = var x
    de-Pat heap[ e⁻ ] = heap[ de-Exp⁻ e⁻ ]

    de-Exp (# x) = # x
    de-Exp (e₁⁻ + e₂⁻) = de-Exp⁻ e₁⁻ ▹ +' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ ∸ e₂⁻) = de-Exp⁻ e₁⁻ ▹ ∸' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ * e₂⁻) = de-Exp⁻ e₁⁻ ▹ *' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ /r e₂⁻) = de-Exp⁻ e₁⁻ ▹ /r' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ %% e₂⁻) = de-Exp⁻ e₁⁻ ▹ %%' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ < e₂⁻) = de-Exp⁻ e₁⁻ ▹ <' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ > e₂⁻) = de-Exp⁻ e₁⁻ ▹ >' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ ≤ e₂⁻) = de-Exp⁻ e₁⁻ ▹ ≤' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ ≥ e₂⁻) = de-Exp⁻ e₁⁻ ▹ ≥' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ =n= e₂⁻) = de-Exp⁻ e₁⁻ ▹ =n=' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ =b= e₂⁻) = de-Exp⁻ e₁⁻ ▹ =b=' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ ∧ e₂⁻) = de-Exp⁻ e₁⁻ ▹ ∧' ◃ de-Exp⁻ e₂⁻
    de-Exp (e₁⁻ ∨ e₂⁻) = de-Exp⁻ e₁⁻ ▹ ∨' ◃ de-Exp⁻ e₂⁻
    de-Exp (¬ e⁻) = ¬ (de-Exp⁻ e⁻)
    de-Exp (p += e⁻) = de-Pat p += de-Exp⁻ e⁻
    de-Exp (p ∸= e⁻) = de-Pat p ∸= de-Exp⁻ e⁻
    de-Exp (p ++) = de-Pat p ++
    de-Exp (p ∸∸) = de-Pat p ∸∸
    de-Exp (p := e⁻) = de-Pat p := de-Exp⁻ e⁻
    de-Exp⁻ {exp} e = de-Exp e
    de-Exp⁻ {pat} p = ! (de-Pat p)

    de-Stmt skip = skip
    de-Stmt (print s e⁻) = print s (de-Exp⁻ e⁻)
    de-Stmt (while e⁻ s⁻) = while (de-Exp⁻ e⁻) (de-Stmt⁻ s⁻)
    de-Stmt (if e⁻ then s₁⁻ else s₂⁻) = if de-Exp⁻ e⁻ then de-Stmt⁻ s₁⁻ else de-Stmt⁻ s₂⁻
    de-Stmt (mkvar' e⁻ k) = C.mkvar (de-Exp⁻ e⁻) λ v → de-Stmt⁻ (k v)
    de-Stmt (s₁⁻ >> s₂⁻) = de-Stmt⁻ s₁⁻ >> de-Stmt⁻ s₂⁻
    de-Stmt⁻ {stmt} s = de-Stmt s
    de-Stmt⁻ {term _ _} e⁻ = exp (de-Exp⁻ e⁻)
