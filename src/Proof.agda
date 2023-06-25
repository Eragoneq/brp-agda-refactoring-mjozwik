open import Language
open import Refactoring_curry
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

private
  variable
    Γ : Ctx
    γ : Env Γ
    t : Ty
    v : Val t
    q : (Γ ⊢ t)

ref-env : Env Γ → Env (ref-ctx Γ)
ref-val : Val t → Val (ref-type t)

ref-env []            = []
ref-env (v ∷ vs)      = (ref-val v) ∷ (ref-env vs)

ref-val unitV         = unitV
ref-val (numV x)      = numV x
ref-val (tupV x x₁)   = tupV (ref-val x) (ref-val x₁)
ref-val (closV x x₁)  = closV (ref-env x) (ref-curry x₁)
ref-val (closV₂ x x₁) = closV (ref-env x) (fun (ref-curry x₁))

lp : (γ : Env Γ) → (x : t ∈ Γ) → lookup-val (ref-env γ) (ref-lookup x) ≡ ref-val (lookup-val γ x)
lp (x ∷ xs) here      = refl
lp (x ∷ xs) (there y) = lp xs y

curry-proof : γ ⊢ q ⇓ v → (ref-env γ) ⊢ (ref-curry q) ⇓ (ref-val v)
curry-proof {γ = γ} v@(⇓var x)          = subst (λ x₁ → _ ⊢ _ ⇓ x₁) (lp γ x) (⇓var (ref-lookup x))
curry-proof ⇓num                        = ⇓num
curry-proof (⇓tup x x₁)                 = ⇓tup (curry-proof x) (curry-proof x₁)
curry-proof (⇓add x x₁)                 = ⇓add (curry-proof x) (curry-proof x₁)
curry-proof (⇓fst x)                    = ⇓fst (curry-proof x)
curry-proof (⇓snd x)                    = ⇓snd (curry-proof x)
curry-proof ⇓fun                        = ⇓fun
curry-proof ⇓fun₂                       = ⇓fun
curry-proof (⇓app x x₁ x₂)              = ⇓app (curry-proof x) (curry-proof x₁) (curry-proof x₂)
curry-proof (⇓app₂ clos arg1 arg2 eval) = ⇓app (⇓app (curry-proof clos) (curry-proof arg2) ⇓fun) (curry-proof arg1) (curry-proof eval)
