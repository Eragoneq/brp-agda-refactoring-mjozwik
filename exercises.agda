module exercises where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-comm; +-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

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

neg : Bool → Bool
neg true = false
neg false = true

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


ex1 : Calc
ex1 = add (num zero) (num (suc zero))

ex2 : Calc
ex2 = mul (add (num zero) (num (suc (suc zero)))) (num (suc (suc (suc zero))))

ex3 : Calc
ex3 = num (suc (suc (suc (suc zero))))

data Val : Set where
  numV : ℕ → Val
  boolV : Bool → Val

data _↓_ : Calc → Val → Set where
  ↓num : ∀ {n} → num n ↓ numV n
  ↓bool : ∀ {v} → bool v ↓ boolV v
  ↓add : ∀ {e1 e2 v1 v2}
       → e1 ↓ (numV v1)
       → e2 ↓ (numV v2)
       → (add e1 e2) ↓ (numV (v1 + v2))
  ↓mul : ∀ {e1 e2 v1 v2}
       → e1 ↓ (numV v1)
       → e2 ↓ (numV v2)
       → (mul e1 e2) ↓ (numV (v1 * v2))
  ↓lt  : ∀ {e1 e2 v1 v2}
       → e1 ↓ (numV v1)
       → e2 ↓ (numV v2)
       → (lt e1 e2) ↓ (boolV (v1 < v2))
  ↓if  : ∀ {e1 e2 e3 v1 v2 v3}
       → e1 ↓ (boolV v1)
       → e2 ↓ v2
       → e3 ↓ v3
       → (if e1 t e2 e e3) ↓ (if v1 then v2 else v3)
  ↓neg : ∀ {e1 v1}
       → e1 ↓ (boolV v1)
       → (¬n e1) ↓ boolV (neg v1)
  ↓and : ∀ {e1 e2 v1 v2}
       → e1 ↓ (boolV v1)
       → e2 ↓ (boolV v2)
       → (e1 ∧ e2) ↓ (boolV (and v1 v2))
  ↓or  : ∀ {e1 e2 v1 v2}
       → e1 ↓ (boolV v1)
       → e2 ↓ (boolV v2)
       → (e1 ∨ e2) ↓ (boolV (or v1 v2))


v1 : Val
v1 = numV (suc zero)

v2 : Val
v2 = numV 6

v3 : Val
v3 = numV 4

↓ex1 : ex1 ↓ v1
↓ex1 = ↓add ↓num ↓num

↓ex2 : ex2 ↓ v2
↓ex2 = ↓mul (↓add ↓num ↓num) ↓num

↓ex3 : ex3 ↓ v3
↓ex3 = ↓num

ex4 : Calc
ex4 = if ((bool false) ∨ (bool true)) t (add (num 3) (num 4)) e (¬n(bool false))

v4 : Val
v4 = numV 7

↓ex4 : ex4 ↓ v4
↓ex4 = ↓if (↓or ↓bool ↓bool) (↓add ↓num ↓num) (↓neg ↓bool)

ex5 : Calc
ex5 = num 1 ∧ num 2

↓ex5 : ∀ {v} → ¬(ex5 ↓ v)
↓ex5 (↓and () ())

ex6 : Calc
ex6 = (add (if (lt (mul (num 2) (num 7)) (num 15)) t (add (num 3) (num 7)) e (mul (num 3) (num 7))) (if (¬n (bool false)) t (num 10) e (num 5)))

v6 : Val
v6 = numV 20

↓ex6 : ex6 ↓ v6
↓ex6 = ↓add (↓if (↓lt (↓mul ↓num ↓num) ↓num) (↓add ↓num ↓num) (↓mul ↓num ↓num)) (↓if (↓neg ↓bool) ↓num ↓num)

data Ty : Set where
  boolT : Ty
  numT  : Ty

data WtCalc : Calc → Ty → Set where
  numₜ  : ∀ {n} → WtCalc (num n) numT
  boolₜ : ∀ {v} → WtCalc (bool v) boolT
  addₜ  : ∀ {e1 e2} → WtCalc e1 numT → WtCalc e2 numT → WtCalc (add e1 e2) numT
  mulₜ  : ∀ {e1 e2} → WtCalc e1 numT → WtCalc e2 numT → WtCalc (mul e1 e2) numT
  ltₜ   : ∀ {e1 e2} → WtCalc e1 numT → WtCalc e2 numT → WtCalc (lt e1 e2) boolT
  ifₜ   : ∀ {e1 e2 e3} → ∀ {t} → WtCalc e1 boolT → WtCalc e2 t → WtCalc e3 t → WtCalc (if e1 t e2 e e3) t
  negₜ  : ∀ {e1} → WtCalc e1 boolT → WtCalc (¬n e1) boolT
  andₜ  : ∀ {e1 e2} → WtCalc e1 boolT → WtCalc e2 boolT → WtCalc (e1 ∧ e2) boolT
  orₜ   : ∀ {e1 e2} → WtCalc e1 boolT → WtCalc e2 boolT → WtCalc (e1 ∨ e2) boolT

ex1ₜ : WtCalc ex1 numT
ex1ₜ = addₜ numₜ numₜ

ex6ₜ : WtCalc ex6 numT
ex6ₜ = addₜ
         (ifₜ (ltₜ (mulₜ numₜ numₜ) numₜ) (addₜ numₜ numₜ) (mulₜ numₜ numₜ))
         (ifₜ (negₜ boolₜ) numₜ numₜ)

dne : Calc → Calc
dne (if x t x₁ e x₂) = if dne x t x₁ e x₂
dne (x ∧ x₁) = dne x ∧ dne x₁
dne (x ∨ x₁) = dne x ∨ dne x₁
dne (num x) = num x
dne (bool x) = bool x
dne (add x x₁) = add (dne x) (dne x₁)
dne (mul x x₁) = mul (dne x) (dne x₁)
dne (lt x x₁) = lt (dne x) (dne x₁)
dne (¬n (¬n x)) = dne x
dne (¬n x) = ¬n (dne x)

wt-ref : ∀ {p : Calc} {t : Ty} → WtCalc p t → WtCalc (dne p) t
wt-ref {num x₁} x = x
wt-ref {bool x₁} x = x
wt-ref (addₜ x x₁) = addₜ (wt-ref x) (wt-ref x₁)
wt-ref (mulₜ x x₁) = mulₜ (wt-ref x) (wt-ref x₁)
wt-ref (ltₜ x x₁) = ltₜ (wt-ref x) (wt-ref x₁)
wt-ref (ifₜ x x₁ x₂) = ifₜ (wt-ref x) x₁ x₂
wt-ref (andₜ x x₁) = andₜ (wt-ref x) (wt-ref x₁)
wt-ref (negₜ (negₜ x)) = wt-ref x
wt-ref (orₜ x x₁) = orₜ (wt-ref x) (wt-ref x₁)
wt-ref (negₜ x) = ?

val-ref : ∀ {p : Calc} {v : Val} → p ↓ v → (dne p) ↓ v
val-ref {p} {v} x = {!!}

ndn-ref : ∀ {p : Calc} → (dne p) ≡ (dne (dne p))
ndn-ref = {!!}

-- data even : ℕ → Set
-- data odd  : ℕ → Set
--
-- data even where
--
--   zero :
--       ---------
--       even zero
--
--   suc  : ∀ {n : ℕ}
--     → odd n
--       ------------
--     → even (suc n)
--
-- data odd where
--
--   suc  : ∀ {n : ℕ}
--     → even n
--       -----------
--     → odd (suc n)
--
--
-- e+e≡e : ∀ {m n : ℕ}
--   → even m
--   → even n
--     ------------
--   → even (m + n)
--
-- o+e≡o : ∀ {m n : ℕ}
--   → odd m
--   → even n
--     -----------
--   → odd (m + n)
--
-- e+e≡e zero     en  =  en
-- e+e≡e (suc om) en  =  suc (o+e≡o om en)
--
-- o+e≡o (suc em) en  =  suc (e+e≡e em en)
--
-- data _≡_ {A : Set} (x : A) : A → Set where
--   refl : x ≡ x
--
-- infix 4 _≡_
--
-- sym : ∀ {A : Set} {x y : A}
--   → x ≡ y
--     -----
--   → y ≡ x
--
-- sym refl = refl
--
-- trans : ∀ {A : Set} {x y z : A}
--   → x ≡ y
--   → y ≡ z
--     -----
--   → x ≡ z
--
-- trans refl refl = refl
