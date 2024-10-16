module muCLL.Context where

open import muCLL.Type

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc)
open import Data.String using (String) renaming (_≟_ to _≟S_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary.Decidable using (Dec; yes; no; isYes; isNo)

Session : Set
Session = String

variable
    x y z : Session

-- Typing context with up to n free type variables
infixr 5 _∷_
data TypeContext (n : ℕ) : Set where
    [] : TypeContext n
    _∷_ : Session × Type n → TypeContext n → TypeContext n

variable
    Δ Δ₁ Δ₂ Γ Γ₁ Γ₂ : TypeContext n

-- Membership of a session name in a type context
infix 4 _∈_
data _∈_ : Session → TypeContext n → Set where
    here  : x ∈ (x , τ) ∷ Δ
    there : x ∈ Δ → x ∈ (y , τ) ∷ Δ

-- Non-membership of a session name in a type context
infix 4 _∉_
data _∉_ : Session → TypeContext n → Set where
    notin : (x ∈ Δ → ⊥) → x ∉ Δ

-- Well-formed type context, i.e., without duplicate session bindings.
-- TODO: this should be used externally, in order to ensure that all contexts are well-formed
data WFTypeContext {n} : TypeContext n → Set where
    [] : WFTypeContext []
    _∷_  : x ∉ Δ → WFTypeContext Δ → WFTypeContext ((x , τ) ∷ Δ)

-- Typing judgement for session names
infix 4 _⊢_
data _⊢_ : TypeContext n → Session × Type n → Set where
    here  : ((x , τ) ∷ Δ) ⊢ (x , τ)
    there : Δ ⊢ (x , τ) → ((y , τ) ∷ Δ) ⊢ (x , τ)

-- Decidable membership of a session name in a type context
infix 4 _∈?_
_∈?_ : (x : Session) → (Δ : TypeContext n) → Dec (x ∈ Δ)
x ∈? [] = no λ()
x ∈? ((y , τ) ∷ Δ) with x ≟S y
...                   | yes refl = yes here
...                   | no ¬p₁ with x ∈? Δ
...                   | yes p₂ = yes (there p₂)
...                   | no ¬p₂ = no λ { here → ¬p₁ refl
                                       ; (there p₂) → ¬p₂ p₂ }

-- Some instancing boilerplate for finding proofs of membership automatically
instance
    ∈?I : {x : Session} {Δ : TypeContext n} → Dec (x ∈ Δ)
    ∈?I {x = x} {Δ} = x ∈? Δ

    ∈I : {x : Session} {Δ : TypeContext n} → {{d : Dec (x ∈ Δ)}} → {{isYes d ≡ true}} → x ∈ Δ
    ∈I {{yes proof}} = proof

    ∉I : {x : Session} {Δ : TypeContext n} → {{d : Dec (x ∈ Δ)}} → {{isNo d ≡ true}} → x ∉ Δ
    ∉I {{no ¬proof}} = notin ¬proof

-- Disjointness of two typing contexts
data Disjoint {n : ℕ} : TypeContext n → TypeContext n → Set where
    [] : Disjoint [] Δ₂
    _∷_ : x ∉ Δ₂ → Disjoint Δ₁ Δ₂ → Disjoint ((x , τ) ∷ Δ₁) Δ₂

-- Decidable disjointness of two typing contexts
disjoint? : (Δ₁ Δ₂ : TypeContext n) → Dec (Disjoint Δ₁ Δ₂)
disjoint? [] Δ₂ = yes []
disjoint? ((x , τ) ∷ Δ₁) Δ₂ with x ∈? Δ₂
...                            | yes p₁ = no λ { ((notin ¬p₁) ∷ _) → ¬p₁ p₁ }
...                            | no ¬p₁ with disjoint? Δ₁ Δ₂
...                            | yes p₂ = yes ((notin ¬p₁) ∷ p₂)
...                            | no ¬p₂ = no λ { (_ ∷ p₂) → ¬p₂ p₂ }

-- Some instancing boilerplate for finding proofs of disjointness automatically
instance
    disjoint?I : {Δ₁ Δ₂ : TypeContext n} → Dec (Disjoint Δ₁ Δ₂)
    disjoint?I {n = n} {Δ₁} {Δ₂} = disjoint? Δ₁ Δ₂

    disjointI : {Δ₁ Δ₂ : TypeContext n} → {{d : Dec (Disjoint Δ₁ Δ₂)}} → {{isYes d ≡ true}} → Disjoint Δ₁ Δ₂
    disjointI {{yes proof}} = proof

-- Proof that the empty context is disjoint from any context (in the opposite direction of the definition)
disjoint[] : {Δ : TypeContext n} → Disjoint Δ []
disjoint[] {Δ = []} = []
disjoint[] {Δ = x ∷ Δ} = notin (λ ()) ∷ disjoint[]

-- Union of two typing contexts - only produces well-formed type contexts if the input contexts are disjoint
join : TypeContext n → TypeContext n → TypeContext n
join [] Δ₂ = Δ₂
join (x ∷ Δ₁) Δ₂ = x ∷ join Δ₁ Δ₂

-- TODO: prove that joining two well-formed contexts produces a well-formed context as long as they're disjoint

-- Boilerplate so that instance search knows that joining anything with an empty context is the identity 
instance
    join[] : {Δ : TypeContext n} → join Δ [] ≡ Δ
    join[] {Δ = []} = refl
    join[] {Δ = x ∷ Δ} rewrite join[] {Δ = Δ} = refl

-- Non-equality of two sessions. Needed this to be a separate type to avoid overlapping instances<
data Different : Session → Session → Set where
    diff : x ≢ y → Different x y

-- Decidable non-equality of two sessions
different? : (x y : Session) → Dec (Different x y)
different? x y with x ≟S y
... | yes p = no λ { (diff ¬p) → ¬p p }
... | no ¬p = yes (diff ¬p)

-- Some instancing boilerplate for finding non-equality proofs automatically
instance
    different?I : {x y : Session} → Dec (Different x y)
    different?I {x = x} {y = y} = different? x y

    differentI : {x y : Session} → {{d : Dec (Different x y)}} → {{isYes d ≡ true}} → Different x y
    differentI {{yes proof}} = proof

-- Increase the number of free type variables in the types of a typing context
injectContext : TypeContext n → TypeContext (suc n)
injectContext [] = [] 
injectContext ((x , τ) ∷ Δ) = (x , injectType τ) ∷ injectContext Δ
