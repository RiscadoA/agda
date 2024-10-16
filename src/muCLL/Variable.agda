module muCLL.Variable where

open import muCLL.Type
open import muCLL.Context

open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_)

-- Variable bindings with up to m variables and where types have up to n free variables
VariableBindings : ℕ → ℕ → Set
VariableBindings n m = Vec (TypeContext n) m

variable
    η η₁ η₂ : VariableBindings n m

-- Increase the number of free type variables in the types of the variable bindings
injectBindings : ∀ {n m} → VariableBindings n m → VariableBindings (suc n) m
injectBindings [] = [] 
injectBindings (Δ ∷ η) = injectContext Δ ∷ injectBindings η
