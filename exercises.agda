module exercises where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-comm; +-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
-- open import Data.String renaming (_<_ to ord)

-- data ℕ : Set where
--   zero : ℕ
--   suc  : ℕ → ℕ
--
-- -- {-# BUILTIN NATURAL ℕ #-}
--
-- _+_ : ℕ → ℕ → ℕ
-- zero + n = n
-- suc m + n = suc (m + n)
--
-- _*_ : ℕ → ℕ → ℕ
-- zero * n = zero
-- suc m * n = n + suc (m * n)

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

_<_ : ℕ → ℕ → Bool
zero  < suc n = true
zero  < zero  = false
suc n < suc m = n < m
suc n < zero  = false

eq : ℕ → ℕ → Bool
eq zero zero = true
eq zero (suc y) = false
eq (suc x) zero = false
eq (suc x) (suc y) = eq x y

neg : Bool → Bool
neg true = false
neg false = true

double-neg : ∀ {b} → b ≡ (neg (neg b))
double-neg {true} = refl
double-neg {false} = refl

and : Bool → Bool → Bool
and true true = true
and true false = false
and false true = false
and false false = false

or : Bool → Bool → Bool
or true true = true
or true false = true
or false true = true
or false false = false

-- infix _<_ 3

Id : Set
Id = ℕ

data Ty : Set where
  unitT : Ty
  boolT : Ty
  numT  : Ty
  funT  : Ty → Ty → Ty

data Calc : Set where
  num  : ℕ → Calc
  bool : Bool → Calc
  add  : Calc → Calc → Calc
  mul  : Calc → Calc → Calc
  lt   : Calc → Calc → Calc
  if_t_e_ : Calc → Calc → Calc → Calc
  ¬n_  : Calc → Calc
  _∧_  : Calc → Calc → Calc
  _∨_  : Calc → Calc → Calc
  lam  : Id → Ty → Calc → Calc
  var  : Id → Calc
  app  : Calc → Calc → Calc


ex1 : Calc
ex1 = add (num zero) (num (suc zero))

ex2 : Calc
ex2 = mul (add (num zero) (num (suc (suc zero)))) (num (suc (suc (suc zero))))

ex3 : Calc
ex3 = num (suc (suc (suc (suc zero))))

data Val : Set where
  unitV : Val
  numV  : ℕ → Val
  boolV : Bool → Val
  closV : Id → Ty → Calc → Val

data Env : Set where
  ∅ : Env
  _,_↦_ : Env → Id → Val → Env

get : Env → Id → Val
get ∅ i = unitV
get (en , x ↦ valₓ) i = if (eq x i) then valₓ else get en i

data _⊢_↓_ : Env → Calc → Val → Set where
  ↓num : ∀ {Γ n} → Γ ⊢ num n ↓ numV n
  ↓bool : ∀ {Γ v} → Γ ⊢ bool v ↓ boolV v
  ↓var : ∀ {Γ v} → Γ ⊢ var v ↓ get Γ v
  ↓add : ∀ {Γ e1 e2 v1 v2}
       → Γ ⊢ e1 ↓ (numV v1)
       → Γ ⊢ e2 ↓ (numV v2)
       → Γ ⊢ (add e1 e2) ↓ (numV (v1 + v2))
  ↓mul : ∀ {Γ e1 e2 v1 v2}
       → Γ ⊢ e1 ↓ (numV v1)
       → Γ ⊢ e2 ↓ (numV v2)
       → Γ ⊢ (mul e1 e2) ↓ (numV (v1 * v2))
  ↓lt  : ∀ {Γ e1 e2 v1 v2}
       → Γ ⊢ e1 ↓ (numV v1)
       → Γ ⊢ e2 ↓ (numV v2)
       → Γ ⊢ (lt e1 e2) ↓ (boolV (v1 < v2))
  ↓if₀ : ∀ {Γ e1 e2 e3 v1 v2 v3}
       → Γ ⊢ e1 ↓ (boolV v1)
       → Γ ⊢ e2 ↓ (boolV v2)
       → Γ ⊢ e3 ↓ (boolV v3)
       → Γ ⊢ (if e1 t e2 e e3) ↓ (boolV (if v1 then v2 else v3))
  ↓if₁ : ∀ {Γ e1 e2 e3 v1 v2 v3}
       → Γ ⊢ e1 ↓ (boolV v1)
       → Γ ⊢ e2 ↓ (numV v2)
       → Γ ⊢ e3 ↓ (numV v3)
       → Γ ⊢ (if e1 t e2 e e3) ↓ (numV (if v1 then v2 else v3))
  ↓neg : ∀ {Γ e1 v1}
       → Γ ⊢ e1 ↓ (boolV v1)
       → Γ ⊢ (¬n e1) ↓ (boolV (neg v1))
  -- ↓neg₀ : ∀ {e1}
  --      → e1 ↓ (boolV true)
  --      → (¬n e1) ↓ (boolV false)
  -- ↓neg₁ : ∀ {e1}
  --      → e1 ↓ (boolV false)
  --      → (¬n e1) ↓ (boolV true)
  ↓and : ∀ {Γ e1 e2 v1 v2}
       → Γ ⊢ e1 ↓ (boolV v1)
       → Γ ⊢ e2 ↓ (boolV v2)
       → Γ ⊢ (e1 ∧ e2) ↓ (boolV (and v1 v2))
  ↓or  : ∀ {Γ e1 e2 v1 v2}
       → Γ ⊢ e1 ↓ (boolV v1)
       → Γ ⊢ e2 ↓ (boolV v2)
       → Γ ⊢ (e1 ∨ e2) ↓ (boolV (or v1 v2))
  ↓fun : ∀ {Γ s t b}
       → Γ ⊢ (lam s t b) ↓ (closV s t b)
  ↓app : ∀ {Γ e1 arg s b t v1 v2}
       → Γ ⊢ e1 ↓ (closV s t b)
       → Γ ⊢ arg ↓ v1
       → (Γ , s ↦ v1) ⊢ b ↓ v2
       → Γ ⊢ (app e1 arg) ↓ v2


v1 : Val
v1 = numV (suc zero)

v2 : Val
v2 = numV 6

v3 : Val
v3 = numV 4

↓ex1 : ∅ ⊢ ex1 ↓ v1
↓ex1 = ↓add ↓num ↓num

↓ex2 : ∅ ⊢ ex2 ↓ v2
↓ex2 = ↓mul (↓add ↓num ↓num) ↓num

↓ex3 : ∅ ⊢ ex3 ↓ v3
↓ex3 = ↓num

ex4 : Calc
ex4 = if ((bool false) ∨ (bool true)) t ((bool false) ∧ (bool true)) e (¬n(bool false))

v4 : Val
v4 = boolV false

↓ex4 : ∅ ⊢ ex4 ↓ v4
↓ex4 = ↓if₀ (↓or ↓bool ↓bool) (↓and ↓bool ↓bool) (↓neg ↓bool)

ex5 : Calc
ex5 = num 1 ∧ num 2

↓ex5 : ∀ {v} → ¬(∅ ⊢ ex5 ↓ v)
↓ex5 (↓and () ())

ex6 : Calc
ex6 = add (if (lt (mul (num 2) (num 7)) (num 15)) t (add (num 3) (num 7)) e (mul (num 3) (num 7))) (if (¬n (bool false)) t (num 10) e (num 5))

v6 : Val
v6 = numV 20

↓ex6 : ∅ ⊢ ex6 ↓ v6
↓ex6 = ↓add (↓if₁ (↓lt (↓mul ↓num ↓num) ↓num) (↓add ↓num ↓num) (↓mul ↓num ↓num)) (↓if₁ (↓neg ↓bool) ↓num ↓num)

ex7 : Calc
ex7 = app (lam 0 numT (add (num 4) (var 0))) (num 3)

v7 : Val
v7 = numV 7

↓ex7 : ∅ ⊢ ex7 ↓ v7
↓ex7 = ↓app ↓fun ↓num (↓add ↓num ↓var)


ex8 : Calc
ex8 = mul (add (num 2) (app (lam 0 numT (add (mul (var 0) (num 0)) (num 1))) (num 42))) (add (num 3) (num 7))

v8 : Val
v8 = numV 30

↓ex8 : ∅ ⊢ ex8 ↓ v8
↓ex8 = ↓mul (↓add ↓num (↓app ↓fun ↓num (↓add (↓mul ↓var ↓num) ↓num))) (↓add ↓num ↓num)

infixl 10 _,_⦂_

data Ctx : Set where
  [] : Ctx
  _,_⦂_ : Ctx → Id → Ty → Ctx

lookup : Ctx → Id → Ty
lookup [] x = unitT
lookup (ctx , x₁ ⦂ xₜ) x = if (eq x x₁) then xₜ else lookup ctx x

data WtCalc : Ctx → Calc → Ty → Set where
  numₜ  : ∀ {ctx n}
        → WtCalc ctx (num n) numT
  boolₜ : ∀ {ctx v}
        → WtCalc ctx (bool v) boolT
  addₜ  : ∀ {ctx e1 e2}
        → WtCalc ctx e1 numT
        → WtCalc ctx e2 numT
        → WtCalc ctx (add e1 e2) numT
  mulₜ  : ∀ {ctx e1 e2}
        → WtCalc ctx e1 numT
        → WtCalc ctx e2 numT
        → WtCalc ctx (mul e1 e2) numT
  ltₜ   : ∀ {ctx e1 e2}
        → WtCalc ctx e1 numT
        → WtCalc ctx e2 numT
        → WtCalc ctx (lt e1 e2) boolT
  ifₜ   : ∀ {ctx e1 e2 e3 t}
        → WtCalc ctx e1 boolT
        → WtCalc ctx e2 t
        → WtCalc ctx e3 t
        → WtCalc ctx (if e1 t e2 e e3) t
  negₜ  : ∀ {ctx e1}
        → WtCalc ctx e1 boolT
        → WtCalc ctx (¬n e1) boolT
  andₜ  : ∀ {ctx e1 e2}
        → WtCalc ctx e1 boolT
        → WtCalc ctx e2 boolT
        → WtCalc ctx (e1 ∧ e2) boolT
  orₜ   : ∀ {ctx e1 e2}
        → WtCalc ctx e1 boolT
        → WtCalc ctx e2 boolT
        → WtCalc ctx (e1 ∨ e2) boolT
  lamₜ  : ∀ {ctx s b t}
        → WtCalc ctx b t
        → WtCalc ctx (lam s t b) (funT (lookup ctx s) t)
  varₜ  : ∀ {ctx s}
        → WtCalc ctx (var s) (lookup ctx s)
  appₜ  : ∀ {ctx f e1 i o}
        → WtCalc ctx f (funT i o)
        → WtCalc ctx e1 i
        → WtCalc ctx (app f e1) o

ex1ₜ : WtCalc [] ex1 numT
ex1ₜ = addₜ numₜ numₜ

ex6ₜ : WtCalc [] ex6 numT
ex6ₜ = addₜ
         (ifₜ (ltₜ (mulₜ numₜ numₜ) numₜ) (addₜ numₜ numₜ) (mulₜ numₜ numₜ))
         (ifₜ (negₜ boolₜ) numₜ numₜ)

ex7ₜ : WtCalc ([] , 1 ⦂ boolT , 0 ⦂ numT) ex7 numT
ex7ₜ = appₜ (lamₜ (addₜ numₜ varₜ)) numₜ

-- dne : Calc → Calc
-- dne (if x t x₁ e x₂) = if dne x t dne x₁ e dne x₂
-- dne (x ∧ x₁) = dne x ∧ dne x₁
-- dne (x ∨ x₁) = dne x ∨ dne x₁
-- dne (num x) = num x
-- dne (bool x) = bool x
-- dne (add x x₁) = add (dne x) (dne x₁)
-- dne (mul x x₁) = mul (dne x) (dne x₁)
-- dne (lt x x₁) = lt (dne x) (dne x₁)
-- dne (¬n (¬n x)) = dne x
-- dne (¬n x) = ¬n (dne x)
--
-- wt-ref : ∀ {p : Calc} {t : Ty} → WtCalc p t → WtCalc (dne p) t
-- wt-ref {num x₁} x = x
-- wt-ref {bool x₁} x = x
-- wt-ref (addₜ x x₁) = addₜ (wt-ref x) (wt-ref x₁)
-- wt-ref (mulₜ x x₁) = mulₜ (wt-ref x) (wt-ref x₁)
-- wt-ref (ltₜ x x₁) = ltₜ (wt-ref x) (wt-ref x₁)
-- wt-ref (ifₜ x x₁ x₂) = ifₜ (wt-ref x) (wt-ref x₁) (wt-ref x₂)
-- wt-ref (andₜ x x₁) = andₜ (wt-ref x) (wt-ref x₁)
-- wt-ref (negₜ (negₜ x)) = wt-ref x
-- wt-ref (orₜ x x₁) = orₜ (wt-ref x) (wt-ref x₁)
-- wt-ref (negₜ boolₜ) = negₜ boolₜ
-- wt-ref (negₜ (ltₜ x x₁)) = negₜ (ltₜ (wt-ref x) (wt-ref x₁))
-- wt-ref (negₜ (ifₜ x x₁ x₂)) = negₜ (ifₜ (wt-ref x) (wt-ref x₁) (wt-ref x₂))
-- wt-ref (negₜ (andₜ x x₁)) = negₜ (andₜ (wt-ref x) (wt-ref x₁))
-- wt-ref (negₜ (orₜ x x₁)) = negₜ (orₜ (wt-ref x) (wt-ref x₁))
--
-- val-ref : ∀ {p : Calc} {v : Val} → p ↓ v → (dne p) ↓ v
-- val-ref ↓num = ↓num
-- val-ref ↓bool = ↓bool
-- val-ref (↓add x x₁) = ↓add (val-ref x) (val-ref x₁)
-- val-ref (↓mul x x₁) = ↓mul (val-ref x) (val-ref x₁)
-- val-ref (↓lt x x₁) = ↓lt (val-ref x) (val-ref x₁)
-- val-ref (↓if₀ x x₁ x₂) = ↓if₀ (val-ref x) (val-ref x₁) (val-ref x₂)
-- val-ref (↓if₁ x x₁ x₂) = ↓if₁ (val-ref x) (val-ref x₁) (val-ref x₂)
-- val-ref (↓neg ↓bool) = ↓neg ↓bool
-- val-ref (↓neg (↓lt x x₁)) = ↓neg (↓lt (val-ref x) (val-ref x₁))
-- val-ref (↓neg (↓if₀ x x₁ x₂)) = ↓neg (↓if₀ (val-ref x) (val-ref x₁) (val-ref x₂))
-- -- val-ref {p} {v} (↓neg (↓neg x)) = subst (_↓_ _) double-neg (val-ref x)
-- val-ref (↓neg (↓neg x)) = subst (λ y → _↓_ _ (boolV y)) double-neg (val-ref x)
-- val-ref (↓neg (↓and x x₁)) = ↓neg (↓and (val-ref x) (val-ref x₁))
-- val-ref (↓neg (↓or x x₁)) = ↓neg (↓or (val-ref x) (val-ref x₁))
-- val-ref (↓and x x₁) = ↓and (val-ref x) (val-ref x₁)
-- val-ref (↓or x x₁) = ↓or (val-ref x) (val-ref x₁)
--
-- ndn-ref : ∀ {p : Calc} → (dne p) ≡ (dne (dne p))
-- ndn-ref = {!!}
