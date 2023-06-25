open import Data.List.Base
open import Data.List.Relation.Unary.All using (All)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; _+_)

infix  8 _,_
infixr 7 _⇒_
infix  6 _⊢_

-- Definition of types used by HLL
data Ty : Set where
  unitT : Ty
  numT  : Ty
  tupT  : Ty → Ty → Ty
  _⇒_   : Ty → Ty → Ty
  /_/_⇒_ : Ty → Ty → Ty → Ty
--  _⭆_   : List Ty → Ty → Ty -- Type used for n-argument functions

-- List of types, with the type of the most recently bound variable on the right
Ctx = List Ty

-- Type definitions for all the required elements
data Env : Ctx → Set
data _⊢_ : Ctx → Ty → Set
data Val : Ty → Set

private
  variable
    Γ Δ : Ctx
    γ : Env Γ
    δ : Env Δ
    n : ℕ
    t u v w : Ty
    v1 : Val t
    v2 : Val u
    l : List Ty

-- Remaining type definition for the big-step semantics
data _⊢_⇓_ : Env Γ → Γ ⊢ t → Val t → Set

-- Definition of a type defining the membership of a list
data _∈_ : Ty → Ctx → Set where
  here  : ∀ {a as} → a ∈ (a ∷ as)
  there : ∀ {a₁ a₂ as} → (a₁ ∈ as) → a₁ ∈ (a₂ ∷ as)

-- Definition of all the language constructs
data _⊢_ where

  -- Basic constructors
  unit :
       Γ ⊢ unitT

  num  :
         ℕ
       → Γ ⊢ numT

  -- Advanced data types

  _,_  :
         Γ ⊢ t
       → Γ ⊢ u
       → Γ ⊢ tupT t u

  -- Arithmetic and operations

  add  :
         Γ ⊢ numT
       → Γ ⊢ numT
       → Γ ⊢ numT

  fst  :
         Γ ⊢ tupT t u
       → Γ ⊢ t

  snd  :
         Γ ⊢ tupT t u
       → Γ ⊢ u

  -- Functions

  var  :
         t ∈ Γ
       ---------------
       → Γ ⊢ t

  fun  :
         (t ∷ Γ) ⊢ u
       ---------------
       → Γ ⊢ (t ⇒ u)

  fun₂ :
       (t ∷ u ∷ Γ) ⊢ v
       --------------------
       → Γ ⊢ (/ t / u ⇒ v)

 --  funₙ :                 -- Definition of the n-argument function construct
 --         (l ++ Γ) ⊢ t
 --       → Γ ⊢ (l ⭆ t)

  app  :
         Γ ⊢ (t ⇒ u)
       → Γ ⊢ t
       ---------
       → Γ ⊢ u

  app₂ :
         Γ ⊢ (/ t / u ⇒ v)
       → Γ ⊢ t
       → Γ ⊢ u
       --------
       → Γ ⊢ v

 -- appₙ :                 -- Definition of the n-argument function application
 --        Γ ⊢ (l ⭆ t)
 --      → All (Γ ⊢_) l
 --      → Γ ⊢ t

-- All of the supported values in HLL
data Val where
  unitV  : Val unitT
  numV   : ℕ → Val numT
  tupV   : Val t → Val u → Val (tupT t u)
  closV  : Env Γ → (t ∷ Γ) ⊢ u → Val (t ⇒ u)
  closV₂ : Env Γ → (t ∷ u ∷ Γ) ⊢ v → Val (/ t / u ⇒ v)
--  closVₙ : Env Γ → (l ++ Γ) ⊢ t → Val

-- Implementation of the Environment
data Env where
  []  : Env []
  _∷_ : Val t → Env Γ → Env (t ∷ Γ)

-- Function used to get the value from the environment
lookup-val : Env Γ → t ∈ Γ → Val t
lookup-val (v ∷ γ) here = v
lookup-val (v ∷ γ) (there x) = lookup-val γ x

-- Implementation of the big-step semantics rules
data _⊢_⇓_ where

  ⇓var  :
          (x : t ∈ Γ)
        → γ ⊢ (var x) ⇓ lookup-val γ x

  ⇓num  :
        γ ⊢ (num n) ⇓ (numV n)

  ⇓tup  : {e1 : _ ⊢ t} {e2 : _ ⊢ u}
        → γ ⊢ e1 ⇓ v1
        → γ ⊢ e2 ⇓ v2
        → γ ⊢ (e1 , e2) ⇓ (tupV v1 v2)

  ⇓add  : ∀ {e1 e2 n1 n2}
        → γ ⊢ e1 ⇓ (numV n1)
        → γ ⊢ e2 ⇓ (numV n2)
        → γ ⊢ (add e1 e2) ⇓ numV (n1 + n2)

  ⇓fst  : {tup : Γ ⊢ tupT t u}
        → γ ⊢ tup ⇓ (tupV v1 v2)
        → γ ⊢ fst tup ⇓ v1

  ⇓snd  : {tup : Γ ⊢ tupT t u}
        → γ ⊢ tup ⇓ (tupV v1 v2)
        → γ ⊢ snd tup ⇓ v2

  ⇓fun  : ∀ {b}
        → γ ⊢ (fun {t} {Γ} {u} b) ⇓ (closV γ b)

  ⇓fun₂ : ∀ {b}
        → γ ⊢ (fun₂ {t} {u} {Γ} {v} b) ⇓ (closV₂ γ b)

  -- ⇓funₙ : ∀ {b}
  --       → γ ⊢ (funₙ {l} {Γ} {t} b) ⇓ (closVₙ γ b)

  ⇓app  : ∀ {f : Γ ⊢ t ⇒ u} {b : (t ∷ Δ) ⊢ u} {arg}
        → γ ⊢ f ⇓ (closV δ b)
        → γ ⊢ arg ⇓ v1
        → (v1 ∷ δ) ⊢ b ⇓ v2
        → γ ⊢ (app f arg) ⇓ v2

  ⇓app₂ : ∀ {f : Γ ⊢ / t / u ⇒ v} {b : (t ∷ u ∷ Δ) ⊢ v} {arg1 arg2 v3}
        → γ ⊢ f ⇓ (closV₂ δ b)
        → γ ⊢ arg1 ⇓ v1
        → γ ⊢ arg2 ⇓ v2
        → (v1 ∷ v2 ∷ δ) ⊢ b ⇓ v3
        → γ ⊢ (app₂ f arg1 arg2) ⇓ v3

  -- ⇓appₙ : ∀ {f : Γ ⊢ l ⭆ t} {b : (l ++ Δ) ⊢ t} {env : Env (l ++ Δ)} {args : List (Γ ⊢ _)} {args_all : All (Γ ⊢_) l} {out} -- Unfinished big-step semantics for n-argument function
  --       → γ ⊢ f ⇓ (closVₙ δ b)
  --       → (ls : All (λ x → γ ⊢ x ⇓ _) args)
  --       → env ⊢ b ⇓ v1
  --       → γ ⊢ (appₙ f args_all) ⇓ v1
