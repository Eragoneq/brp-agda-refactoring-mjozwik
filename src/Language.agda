open import Data.List.Base
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; _+_)

data Ty : Set where
  unitT : Ty
  numT  : Ty
--  boolT : Ty
  _⇒_   : Ty → Ty → Ty

-- List of types, with the type of the most recently bound variable on the right
Ctx = List Ty

data _∈_ : Ty → Ctx → Set where
  here  : ∀ {a as} → a ∈ (a ∷ as)
  there : ∀ {a₁ a₂ as} → (a₁ ∈ as) → a₁ ∈ (a₂ ∷ as)

data _⊢_ : Ctx → Ty → Set where
  t    : ∀ {Γ}
       → Γ ⊢ unitT

  num  : ∀ {Γ}
       → ℕ
       → Γ ⊢ numT

  add  : ∀ {Γ}
       → Γ ⊢ numT
       → Γ ⊢ numT
       → Γ ⊢ numT

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
  ↓add  : ∀ {Γ} {γ : Env Γ} {e1 e2 v1 v2}
        → γ ⊢ e1 ↓ (numV v1)
        → γ ⊢ e2 ↓ (numV v2)
        → γ ⊢ (add e1 e2) ↓ numV (v1 + v2)
  ↓fun  : ∀ {Γ} {γ : Env Γ} {t u b}
        → γ ⊢ (fun {Γ} {t} {u} b) ↓ (closV γ b)
  ↓app  : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} {t u : Ty} {f : Γ ⊢ (t ⇒ u)} {b : (t ∷ Δ) ⊢ u} {arg} {v1 v2}
        → γ ⊢ f ↓ (closV δ b)
        → γ ⊢ arg ↓ v1
        → (v1 `∷ δ) ⊢ b ↓ v2
        → γ ⊢ (app f arg) ↓ v2

ex1 : [] ⊢ numT
ex1 = add (num 1) (num 2)

v1 : Val
v1 = numV 3

↓ex1 : ∅ ⊢ ex1 ↓ v1
↓ex1 = ↓add ↓num ↓num

ex2 : [] ⊢ numT
ex2 = (app (fun (add (num 1) (var here))) (num 2))

v2 : Val
v2 = numV 3

↓ex2 : ∅ ⊢ ex2 ↓ v2
↓ex2 = ↓app ↓fun ↓num (↓add ↓num (↓var here))
