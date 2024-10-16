module muCLL.Process where

open import muCLL.Type
open import muCLL.Context
open import muCLL.Variable

open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using ([]; _∷_; lookup)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Process with n free type variables, m free recursion variables,
-- linear typing context Δ, exponential typing context Γ and recursion variable bindings η 
data Process : {n m : ℕ} (Δ Γ : TypeContext n) (η : VariableBindings n m) → Set where
    -- Inaction
    ina : {τ : TypeContext n} → Process {n} [] τ η

    -- Forwarding, parallel composition and cut
    fwd : (x y : Session)
        → {{Different x y}}
        → Process ((x , dual τ) ∷ (y , τ) ∷ []) Γ η
    par : Process Δ₁ Γ η 
        → Process Δ₂ Γ η
        → {{Disjoint Δ₁ Δ₂}}
        → Process (join Δ₁ Δ₂) Γ η
    cut : (x : Session)
        → Process ((x , τ) ∷ Δ₁) Γ η
        → Process ((x , dual τ) ∷ Δ₂) Γ η
        → {{Disjoint Δ₁ Δ₂}} → {{join Δ₁ Δ₂ ≡ Δ}}
        → Process Δ Γ η

    -- Close and wait
    close : (x : Session)
          → Process ((x , one) ∷ []) Γ η
    wait : (x : Session)
         → Process Δ Γ η
         → {{x ∉ Δ}}
         → Process ((x , bot) ∷ Δ) Γ η

    -- Offer and choice (with only two possible labels, inl and inr)
    inl : (x : Session)
        → Process ((x , τ₁) ∷ Δ) Γ η
        → Process ((x , τ₁ ⊕ τ₂) ∷ Δ) Γ η
    inr : (x : Session)
        → Process ((x , τ₂) ∷ Δ) Γ η
        → Process ((x , τ₁ ⊕ τ₂) ∷ Δ) Γ η
    case : (x : Session)
         → (inl : Process ((x , τ₁) ∷ Δ) Γ η)
         → (inr : Process ((x , τ₂) ∷ Δ) Γ η)
         → Process ((x , τ₁ & τ₂) ∷ Δ) Γ η

    -- Send and receive
    send : (x y : Session)
         → Process ((y , τ₁) ∷ Δ₁) Γ η
         → Process ((x , τ₂) ∷ Δ₂) Γ η
         → {{Different x y}} → {{Disjoint Δ₁ Δ₂}}
         → Process ((x , τ₁ ⊗ τ₂) ∷ join Δ₁ Δ₂) Γ η
    recv : (x z : Session)
         → Process ((z , τ₁) ∷ (x , τ₂) ∷ Δ) Γ η
         → {{Different x z}} → {{x ∉ Δ}}
         → Process ((x , τ₁ ⅋ τ₂) ∷ Δ) Γ η

    -- Replication (!), unrestriction (?) and call
    repl : (x y : Session)
         → Process ((y , τ) ∷ []) Γ η
         → Process ((x , ‼ τ) ∷ []) Γ η
    unres : (x : Session)
          → Process Δ ((x , τ) ∷ Γ) η
          → {{x ∉ Δ}}
          → Process ((x , ⁇ τ) ∷ Δ) Γ η
    call : (x z : Session)
         → Process ((z , τ) ∷ Δ) ((x , τ) ∷ Γ) η
         → {{Different x z}} → {{x ∉ Γ}}
         → Process Δ ((x , τ) ∷ Γ) η

    -- Universal and existential process types
    sendty : (x : Session)
           → (τs : Type n)
           → Process ((x , substType τs τ) ∷ Δ) Γ η
           → Process ((x , ∃| τ) ∷ Δ) Γ η
    recvty : (x : Session)
           → Process ((x , τ) ∷ injectContext Δ) (injectContext Γ) (injectBindings η)
           → Process ((x , ∀| τ) ∷ Δ) Γ η

    -- Recursive and corecursive process types
    corec : (x : Session)
          → Process ((x , τ) ∷ (injectContext Δ)) (injectContext Γ) (((x , var zero) ∷ (injectContext Δ)) ∷ injectBindings η)
          → Process ((x , ν| τ) ∷ Δ) Γ η
    unfold-μ : (x : Session)
             → Process ((x , substType (μ| τ) τ) ∷ Δ) (Γ) (η)
             → Process ((x , μ| τ) ∷ Δ) Γ η
    unfold-ν : (x : Session)
             → Process ((x , substType (ν| τ) τ) ∷ Δ) (Γ) (η)
             → Process ((x , ν| τ) ∷ Δ) Γ η
    var : (i : Fin m)
        → Process (lookup η i) Γ η

variable
    P Q R : Process Δ Γ η

-- Define some syntactic sugar for the process constructors
syntax par P Q = par [ P || Q ]
syntax cut x P Q = cut [ P ]: x :[ Q ]
syntax wait x P = wait x / P
syntax inl x P = inl x / P
syntax inr x P = inr x / P
syntax case x P Q = case x [ |inl| P |inr| Q ]
syntax send x y P Q = send x [ y :| P ] / Q
syntax recv x z P = recv x [ z ] / P
syntax repl x y P = ‼ x [ y ] / P
syntax unres x P = ⁇ x / P
syntax call x z P = call x [ z ] / P
syntax sendty x τs P = sendty x [ τs ] / P
syntax recvty x P = recvty x / P
syntax corec x P = corec x / P
syntax unfold-μ x P = unfold-μ x / P
syntax unfold-ν x P = unfold-ν x / P

-- cut! doesn't have its own constructor since it can be defined in terms of cut, repl and wait
cut!'aux : Process ((x , τ) ∷ Δ) Γ η → Process ((x , dual (dual τ)) ∷ Δ) Γ η
cut!'aux {τ = τ} P rewrite dualInvolutive τ = P
cut!' : (x y : Session)
      → Process ((y , τ) ∷ []) Γ η
      → Process Δ ((x , dual τ) ∷ Γ) η
      → {{x ∉ Γ}} → {{x ∉ Δ}}
      → Process Δ Γ η
cut!' x y P Q {{_}} {{x∉Δ}} = cut x (unres x Q {{x∉Δ}}) (repl x y (cut!'aux P)) {{disjoint[]}}
syntax cut!' x y P Q = cut! [ y :| P ]: x :[ Q ]

-- So that we can help the type checker with the complicated stuff
hintΔ_/_ : {n m : ℕ} → {Δ₁ Γ : TypeContext n} {η : VariableBindings n m} → (Δ₂ : TypeContext n) → {{Δ₁ ≡ Δ₂}} → Process Δ₁ Γ η → Process Δ₂ Γ η
hintΔ_/_ Δ₂ {{refl}} P = P

-- Same as above, but for the exponential typing context
hintΓ_/_ : {n m : ℕ} → {Γ₁ Δ : TypeContext n} {η : VariableBindings n m} → (Γ₂ : TypeContext n) → {{Γ₁ ≡ Γ₂}} → Process Δ Γ₁ η → Process Δ Γ₂ η
hintΓ_/_ Γ₂ {{refl}} P = P

-- A process which has no free variables of any kind, empty typing contexts and no recursion variable bindings
ClosedProcess = Process {0} {0} [] [] []

-- Many examples of closed processes using the syntax sugar defined above

ex-ina : ClosedProcess
ex-ina =
    par [
        ina
    ||
        ina
    ]

ex-close-wait : ClosedProcess
ex-close-wait =
    cut [
        close "x"
    ]: "x" :[
        wait "x" /
        ina
    ]

ex-fwd : ClosedProcess
ex-fwd =
    cut [
        cut [
            close "y"
        ]: "y" :[
            fwd "y" "x"
        ]
    ]: "x" :[
        wait "x" /
        ina
    ]

ex-case : ClosedProcess
ex-case =
    cut [
        inl "x" /
        close "x"
    ]: "x" :[
        case "x" [
            |inl|
                wait "x" /
                ina
            |inr|
                close "x"
        ]
    ]

ex-par : ClosedProcess
ex-par =
    cut [
        par [
            close "x"
        ||
            ina
        ]
    ]: "x" :[
        par [
            ina 
        ||
            wait "x" /
            ina
        ]
    ]

ex-send-recv : ClosedProcess
ex-send-recv =
    cut [
        send "x" [ "y" :|
            wait "y" /
            ina
        ] /
        close "x"
    ]: "x" :[
        recv "x" [ "y" ] /
        par [
            close "y"
        ||
            wait "x" /
            ina
        ]
    ]

ex-‼-⁇-call : ClosedProcess
ex-‼-⁇-call =
    cut [
        ‼ "x" [ "y" ] /
        close "y"
    ]: "x" :[
        ⁇ "x" /
        call "x" [ "y" ] /
        call "x" [ "z" ] /
        wait "z" /
        wait "y" /
        ina
    ]

ex-cut! : ClosedProcess
ex-cut! =
    cut! [
        "y" :|
        wait "y" /
        ina
    ]: "x" :[
        par [
            call "x" [ "z" ] /
            close "z"
        ||
            call "x" [ "z" ] /
            close "z"
        ]
    ]

ex-sendty : ClosedProcess
ex-sendty =
    cut [
        sendty "x" [ one ] /
        wait "x" /
        ina
    ]: "x" :[
        recvty "x" /
        close "x"
    ]

ex-generic-fwd-test : ClosedProcess
ex-generic-fwd-test =
    cut! [
        "fwd" :|
        hintΔ ("fwd" , ∀| (var zero ⅋ dualVar zero)) ∷ [] /
        recvty "fwd" /
        recv "fwd" [ "x" ] /
        fwd "x" "fwd"
    ]: "fwd" :[
        call "fwd" [ "fwd1" ] /
        sendty "fwd1" [ one ] /
        send "fwd1" [ "x" :| wait "x" / ina ] /
        close "fwd1"
    ]

ex-corec : ClosedProcess
ex-corec =
    cut [
        hintΔ ("x" , μ| (one ⊕ var zero)) ∷ [] /
        unfold-μ "x" /
        inr "x" /
        unfold-μ "x" /
        inl "x" /
        close "x"
    ]: "x" :[
        corec "x" /
        case "x" [
            |inl|
                wait "x" /
                ina
            |inr|
                var zero
        ]
    ]
