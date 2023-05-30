open import Data.List.Base
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; _+_)

-- infix  8 _,_:=_,_
infix  8 _,_
infixr 7 _⇒_
infix  6 _⊢_

data Ty : Set where
  unitT : Ty
  numT  : Ty
--  boolT : Ty
  tupT  : Ty → Ty → Ty
  _⇒_   : Ty → Ty → Ty

-- List of types, with the type of the most recently bound variable on the right
Ctx = List Ty

private
  variable
    Γ Δ : Ctx

data _∈_ : Ty → Ctx → Set where
  here  : ∀ {a as} → a ∈ (a ∷ as)
  there : ∀ {a₁ a₂ as} → (a₁ ∈ as) → a₁ ∈ (a₂ ∷ as)

data _⊢_ : Ctx → Ty → Set where
  -- Basic constructors
  unit : ∀ {Γ}
       → Γ ⊢ unitT

  num  : ∀ {Γ}
       → ℕ
       → Γ ⊢ numT

  -- Advanced data types

  -- _,_:=
  _,_  : ∀ {Γ t u}
    -- → (t u : Ty)
       → Γ ⊢ t
       → Γ ⊢ u
       → Γ ⊢ tupT t u

  -- Arithmetic and operations

  add  : ∀ {Γ}
       → Γ ⊢ numT
       → Γ ⊢ numT
       → Γ ⊢ numT

  fst  : ∀ {Γ t u}
       → Γ ⊢ tupT t u
       → Γ ⊢ t

  snd  : ∀ {Γ t u}
       → Γ ⊢ tupT t u
       → Γ ⊢ u

  -- Functions

  var  : ∀ {Γ t}
       → t ∈ Γ
       ---------------
       → Γ ⊢ t

  fun  : ∀ {Γ t u}
       → (t ∷ Γ) ⊢ u
       ---------------
       → Γ ⊢ (t ⇒ u)

  app  : ∀ {Γ t u}
       → Γ ⊢ (t ⇒ u)
       → Γ ⊢ t
       ---------
       → Γ ⊢ u

Env : Ctx → Set

data Val : Set where
  unitV : Val
  numV  : ℕ → Val
  tupV  : Val → Val → Val
  closV : ∀ {Γ t u} → Env Γ → (t ∷ Γ) ⊢ u → Val

Env Γ = {t : Ty} → t ∈ Γ → Val

∅ : Env []
∅ ()

_`∷_ : ∀ {Γ t} → Val → Env Γ → Env (t ∷ Γ)
(v `∷ γ) here = v
(v `∷ γ) (there x) = γ x

data _⊢_↓_ : {Γ : Ctx} {t : Ty} → Env Γ → Γ ⊢ t → Val → Set where

  ↓var  : ∀ {Γ} {γ : Env Γ} {t : Ty}
        → (x : t ∈ Γ)
        → γ ⊢ (var x) ↓ γ x

  ↓num  : ∀ {Γ} {γ : Env Γ} {n}
        → γ ⊢ (num n) ↓ (numV n)

  ↓tup  : ∀ {Γ} {γ : Env Γ} {t u : Ty} {e1 : _ ⊢ t} {e2 : _ ⊢ u} {v1 v2} 
        → γ ⊢ e1 ↓ v1
        → γ ⊢ e2 ↓ v2
        → γ ⊢ (e1 , e2) ↓ (tupV v1 v2)

  ↓add  : ∀ {Γ} {γ : Env Γ} {e1 e2 v1 v2}
        → γ ⊢ e1 ↓ (numV v1)
        → γ ⊢ e2 ↓ (numV v2)
        → γ ⊢ (add e1 e2) ↓ numV (v1 + v2)

  ↓fst  : ∀ {Γ} {γ : Env Γ} {t u : Ty} {tup : Γ ⊢ tupT t u} {v1 v2}
        → γ ⊢ tup ↓ (tupV v1 v2)
        → γ ⊢ fst tup ↓ v1
        -- → γ ⊢ e1 ↓ v1
        -- → γ ⊢ e2 ↓ v2
        -- → γ ⊢ fst (e1 , e2) ↓ v1

  ↓snd  : ∀ {Γ} {γ : Env Γ} {t u : Ty} {tup : Γ ⊢ tupT t u} {v1 v2}
        → γ ⊢ tup ↓ (tupV v1 v2)
        → γ ⊢ snd tup ↓ v2
        -- → γ ⊢ e1 ↓ v1
        -- → γ ⊢ e2 ↓ v2
        -- → γ ⊢ snd (e1 , e2) ↓ v2

  ↓fun  : ∀ {Γ} {γ : Env Γ} {t u b}
        → γ ⊢ (fun {Γ} {t} {u} b) ↓ (closV γ b)

  ↓app  : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} {t u : Ty} {f : Γ ⊢ t ⇒ u} {b : (t ∷ Δ) ⊢ u} {arg} {v1 v2}
        → γ ⊢ f ↓ (closV δ b)
        → γ ⊢ arg ↓ v1
        → (v1 `∷ δ) ⊢ b ↓ v2
        → γ ⊢ (app f arg) ↓ v2
