module muCLL.Type where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Relation.Nullary.Decidable using (yes; no)
open import Data.Nat renaming (_≟_ to _≟ℕ_) using (suc; ℕ)
open import Data.Fin using (Fin; toℕ; inject₁; lower₁)
open import Data.Empty using (⊥-elim)

-- Session type with up to n free type variables
data Type (n : ℕ) : Set where
    var : (i : Fin n) → Type n
    dualVar : (i : Fin n) → Type n
    one : Type n
    bot : Type n
    _⊗_ : Type n → Type n → Type n
    _⅋_ : Type n → Type n → Type n
    _⊕_ : Type n → Type n → Type n
    _&_ : Type n → Type n → Type n
    ‼_ : Type n → Type n
    ⁇_ : Type n → Type n
    ∃|_ : Type (suc n) → Type n
    ∀|_ : Type (suc n) → Type n
    μ|_ : Type (suc n) → Type n
    ν|_ : Type (suc n) → Type n

variable
    n m : ℕ
    i j : Fin n
    τ τ₁ τ₂ : Type n

-- Given a type τ, flip it's last (n - 1) free type variable's duality
substDualTypeVar : {n : ℕ} → Type n → Type n
substDualTypeVar {n} (var i) with n ≟ℕ suc (toℕ i)
...                             | yes _ = dualVar i
...                             | no  _ = var i
substDualTypeVar {n} (dualVar i) with n ≟ℕ suc (toℕ i)
...                                 | yes _ = var i
...                                 | no  _ = dualVar i
substDualTypeVar one = one
substDualTypeVar bot = bot
substDualTypeVar (τ₁ ⊗ τ₂) = substDualTypeVar τ₁ ⊗ substDualTypeVar τ₂
substDualTypeVar (τ₁ ⅋ τ₂) = substDualTypeVar τ₁ ⅋ substDualTypeVar τ₂
substDualTypeVar (τ₁ ⊕ τ₂) = substDualTypeVar τ₁ ⊕ substDualTypeVar τ₂
substDualTypeVar (τ₁ & τ₂) = substDualTypeVar τ₁ & substDualTypeVar τ₂
substDualTypeVar (‼ τ) = ‼ (substDualTypeVar τ)
substDualTypeVar (⁇ τ) = ⁇ (substDualTypeVar τ)
substDualTypeVar (∃| τ) = ∃| (substDualTypeVar τ)
substDualTypeVar (∀| τ) = ∀| (substDualTypeVar τ)
substDualTypeVar (μ| τ) = μ| (substDualTypeVar τ)
substDualTypeVar (ν| τ) = ν| (substDualTypeVar τ)

-- Given a type τ, return its dual
dual : Type n → Type n
dual (var i) = dualVar i
dual (dualVar i) = var i
dual one = bot
dual bot = one
dual (τ₁ ⊗ τ₂) = dual τ₁ ⅋ dual τ₂
dual (τ₁ ⅋ τ₂) = dual τ₁ ⊗ dual τ₂
dual (τ₁ ⊕ τ₂) = dual τ₁ & dual τ₂
dual (τ₁ & τ₂) = dual τ₁ ⊕ dual τ₂
dual (‼ τ) = ⁇ (dual τ)
dual (⁇ τ) = ‼ (dual τ)
dual (∃| τ) = ∀| dual τ
dual (∀| τ) = ∃| dual τ
dual (μ| τ) = ν| substDualTypeVar (dual τ)
dual (ν| τ) = μ| substDualTypeVar (dual τ)

-- Proof that substDualTypeVar is involutive
substDualTypeVarInvolutive : (τ : Type n) → substDualTypeVar (substDualTypeVar τ) ≡ τ
substDualTypeVarInvolutive {n = n} (var i) with n ≟ℕ suc (toℕ i)
...                                           | yes p with n ≟ℕ suc (toℕ i)
...                                                      | yes p = refl
...                                                      | no ¬p = ⊥-elim (¬p p)
substDualTypeVarInvolutive {n = n} (var i)    | no ¬p with n ≟ℕ suc (toℕ i)
...                                                      | yes p = ⊥-elim (¬p p)
...                                                      | no ¬p = refl
substDualTypeVarInvolutive {n = n} (dualVar i) with n ≟ℕ suc (toℕ i)
...                                               | yes p with n ≟ℕ suc (toℕ i)
...                                                          | yes p = refl
...                                                          | no ¬p = ⊥-elim (¬p p)
substDualTypeVarInvolutive {n = n} (dualVar i) | no ¬p with n ≟ℕ suc (toℕ i)
...                                                          | yes p = ⊥-elim (¬p p)
...                                                          | no ¬p = refl
substDualTypeVarInvolutive one = refl
substDualTypeVarInvolutive bot = refl
substDualTypeVarInvolutive (τ₁ ⊗ τ₂) rewrite substDualTypeVarInvolutive τ₁ | substDualTypeVarInvolutive τ₂ = refl
substDualTypeVarInvolutive (τ₁ ⅋ τ₂) rewrite substDualTypeVarInvolutive τ₁ | substDualTypeVarInvolutive τ₂ = refl
substDualTypeVarInvolutive (τ₁ ⊕ τ₂) rewrite substDualTypeVarInvolutive τ₁ | substDualTypeVarInvolutive τ₂ = refl
substDualTypeVarInvolutive (τ₁ & τ₂) rewrite substDualTypeVarInvolutive τ₁ | substDualTypeVarInvolutive τ₂ = refl
substDualTypeVarInvolutive (‼ τ) rewrite substDualTypeVarInvolutive τ = refl
substDualTypeVarInvolutive (⁇ τ) rewrite substDualTypeVarInvolutive τ = refl
substDualTypeVarInvolutive (∃| τ) rewrite substDualTypeVarInvolutive τ = refl
substDualTypeVarInvolutive (∀| τ) rewrite substDualTypeVarInvolutive τ = refl
substDualTypeVarInvolutive (μ| τ) rewrite substDualTypeVarInvolutive τ = refl
substDualTypeVarInvolutive (ν| τ) rewrite substDualTypeVarInvolutive τ = refl

-- Proof that substDualTypeVar commutes with dual
substDualTypeVarDualCom : {n : ℕ} (τ : Type n) → dual (substDualTypeVar τ) ≡ substDualTypeVar (dual τ)
substDualTypeVarDualCom {n} (var i) with n ≟ℕ suc (toℕ i)
...                                     | yes _ = refl
...                                     | no  _ = refl
substDualTypeVarDualCom {n} (dualVar i) with n ≟ℕ suc (toℕ i)
...                                         | yes _ = refl
...                                         | no  _ = refl
substDualTypeVarDualCom one = refl
substDualTypeVarDualCom bot = refl
substDualTypeVarDualCom (τ₁ ⊗ τ₂) rewrite substDualTypeVarDualCom τ₁ | substDualTypeVarDualCom τ₂ = refl
substDualTypeVarDualCom (τ₁ ⅋ τ₂) rewrite substDualTypeVarDualCom τ₁ | substDualTypeVarDualCom τ₂ = refl
substDualTypeVarDualCom (τ₁ ⊕ τ₂) rewrite substDualTypeVarDualCom τ₁ | substDualTypeVarDualCom τ₂ = refl
substDualTypeVarDualCom (τ₁ & τ₂) rewrite substDualTypeVarDualCom τ₁ | substDualTypeVarDualCom τ₂ = refl
substDualTypeVarDualCom (‼ τ) rewrite substDualTypeVarDualCom τ = refl
substDualTypeVarDualCom (⁇ τ) rewrite substDualTypeVarDualCom τ = refl
substDualTypeVarDualCom (∃| τ) rewrite substDualTypeVarDualCom τ = refl
substDualTypeVarDualCom (∀| τ) rewrite substDualTypeVarDualCom τ = refl
substDualTypeVarDualCom (μ| τ) rewrite substDualTypeVarDualCom τ = refl
substDualTypeVarDualCom (ν| τ) rewrite substDualTypeVarDualCom τ = refl

-- Proof that dual is involutive
dualInvolutive : (τ : Type n) → dual (dual τ) ≡ τ
dualInvolutive (var i) = refl
dualInvolutive (dualVar i) = refl
dualInvolutive one = refl
dualInvolutive bot = refl
dualInvolutive (τ₁ ⊗ τ₂) rewrite dualInvolutive τ₁ | dualInvolutive τ₂ = refl
dualInvolutive (τ₁ ⅋ τ₂) rewrite dualInvolutive τ₁ | dualInvolutive τ₂ = refl
dualInvolutive (τ₁ ⊕ τ₂) rewrite dualInvolutive τ₁ | dualInvolutive τ₂ = refl
dualInvolutive (τ₁ & τ₂) rewrite dualInvolutive τ₁ | dualInvolutive τ₂ = refl
dualInvolutive (‼ τ) rewrite dualInvolutive τ = refl
dualInvolutive (⁇ τ) rewrite dualInvolutive τ = refl
dualInvolutive (∃| τ) rewrite dualInvolutive τ = refl
dualInvolutive (∀| τ) rewrite dualInvolutive τ = refl
dualInvolutive (μ| τ) rewrite sym (substDualTypeVarDualCom (substDualTypeVar (dual τ))) =
    cong μ|_ (trans (cong dual (substDualTypeVarInvolutive (dual τ))) (dualInvolutive τ))
dualInvolutive (ν| τ) rewrite sym (substDualTypeVarDualCom (substDualTypeVar (dual τ))) =
    cong ν|_ (trans (cong dual (substDualTypeVarInvolutive (dual τ))) (dualInvolutive τ))

-- Increase the number of free type variables in a type by one, without changing the type itself
injectType : {n : ℕ} → Type n → Type (suc n)
injectType (var i) = var (inject₁ i)
injectType (dualVar i) = dualVar (inject₁ i)
injectType one = one
injectType bot = bot
injectType (τ₁ ⊗ τ₂) = injectType τ₁ ⊗ injectType τ₂
injectType (τ₁ ⅋ τ₂) = injectType τ₁ ⅋ injectType τ₂
injectType (τ₁ ⊕ τ₂) = injectType τ₁ ⊕ injectType τ₂
injectType (τ₁ & τ₂) = injectType τ₁ & injectType τ₂
injectType (‼ τ) = ‼ injectType τ
injectType (⁇ τ) = ⁇ injectType τ
injectType (∃| τ) = ∃| injectType τ
injectType (∀| τ) = ∀| injectType τ
injectType (μ| τ) = μ| injectType τ
injectType (ν| τ) = ν| injectType τ

-- Substitute the n-th free type variable in a type with τ. We end up with one less free type variable.
substType : {n : ℕ} → Type n → Type (suc n) → Type n
substType {n} τ (var i) with n ≟ℕ toℕ i
...                        | yes p = τ
...                        | no ¬p = var (lower₁ i ¬p)
substType {n} τ (dualVar i) with n ≟ℕ toℕ i
...                            | yes p = dual τ
...                            | no ¬p = dualVar (lower₁ i ¬p)
substType τ one = one
substType τ bot = bot
substType τ (τ₁ ⊗ τ₂) = substType τ τ₁ ⊗ substType τ τ₂
substType τ (τ₁ ⅋ τ₂) = substType τ τ₁ ⅋ substType τ τ₂
substType τ (τ₁ ⊕ τ₂) = substType τ τ₁ ⊕ substType τ τ₂
substType τ (τ₁ & τ₂) = substType τ τ₁ & substType τ τ₂
substType τ (‼ τ₁) = ‼ substType τ τ₁
substType τ (⁇ τ₁) = ⁇ substType τ τ₁
substType τ (∃| τ₁) = ∃| substType (injectType τ) τ₁
substType τ (∀| τ₁) = ∀| substType (injectType τ) τ₁
substType τ (μ| τ₁) = μ| substType (injectType τ) τ₁
substType τ (ν| τ₁) = ν| substType (injectType τ) τ₁
