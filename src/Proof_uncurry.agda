open import Language
open import Refactoring_uncurry
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Examples

private
  variable
    Γ : Ctx
    γ : Env Γ
    t : Ty
    v : Val t
    q : (Γ ⊢ t)

ref-env : Env Γ → Env Γ
ref-val : Val t → Val t

ref-env []       = []
ref-env (v ∷ vs) = (ref-val v) ∷ (ref-env vs)

ref-val unitV         = unitV
ref-val (numV x)      = numV x
ref-val (tupV x x₁)   = tupV (ref-val x) (ref-val x₁)
-- ref-val (closV x (fun y))  = closV₂ (ref-env x) (ref-uncurry y)
ref-val (closV x x₁)  = closV (ref-env x) (ref-uncurry x₁)
ref-val (closV₂ x x₁) = closV₂ (ref-env x) (ref-uncurry x₁)

lp : (γ : Env Γ) → (x : t ∈ Γ) → lookup-val (ref-env γ) x ≡ ref-val (lookup-val γ x)
lp (x ∷ xs) here = refl
lp (x ∷ xs) (there y) = lp xs y

uncurry-proof : γ ⊢ q ⇓ v → (ref-env γ) ⊢ (ref-uncurry q) ⇓ (ref-val v)
uncurry-proof {γ = γ} v@(⇓var x)                                          = subst (λ x₁ → _ ⊢ _ ⇓ x₁) (lp γ x) (⇓var x)
uncurry-proof ⇓num                                                      = ⇓num
uncurry-proof (⇓tup x x₁)                                               = ⇓tup (uncurry-proof x) (uncurry-proof x₁)
uncurry-proof (⇓add x x₁)                                               = ⇓add (uncurry-proof x) (uncurry-proof x₁)
uncurry-proof (⇓fst x)                                                  = ⇓fst (uncurry-proof x)
uncurry-proof (⇓snd x)                                                  = ⇓snd (uncurry-proof x)
uncurry-proof ⇓fun                                                      = ⇓fun
uncurry-proof ⇓fun₂                                                     = ⇓fun₂
uncurry-proof (⇓app (⇓app {f = fst f} x arg2 y) arg1 eval)              = ⇓app (⇓app (uncurry-proof x) (uncurry-proof arg2) (uncurry-proof y)) (uncurry-proof arg1) (uncurry-proof eval)
uncurry-proof (⇓app (⇓app {f = snd f} x arg2 y) arg1 eval)              = ⇓app (⇓app (uncurry-proof x) (uncurry-proof arg2) (uncurry-proof y)) (uncurry-proof arg1) (uncurry-proof eval)
uncurry-proof (⇓app (⇓app {f = var x₁} x arg2 y) arg1 eval)             = ⇓app (⇓app (uncurry-proof x) (uncurry-proof arg2) (uncurry-proof y)) (uncurry-proof arg1) (uncurry-proof eval)
uncurry-proof (⇓app (⇓app {f = fun (fst f)} x arg2 y) arg1 eval)        = ⇓app (⇓app (uncurry-proof x) (uncurry-proof arg2) (uncurry-proof y)) (uncurry-proof arg1) (uncurry-proof eval)
uncurry-proof (⇓app (⇓app {f = fun (snd f)} x arg2 y) arg1 eval)        = ⇓app (⇓app (uncurry-proof x) (uncurry-proof arg2) (uncurry-proof y)) (uncurry-proof arg1) (uncurry-proof eval)
uncurry-proof (⇓app (⇓app {f = fun (var x₁)} x arg2 y) arg1 eval)       = ⇓app (⇓app (uncurry-proof x) (uncurry-proof arg2) (uncurry-proof y)) (uncurry-proof arg1) (uncurry-proof eval)
uncurry-proof (⇓app (⇓app {f = fun (fun f)} x arg2 y) arg1 eval)        = ⇓app₂ ⇓fun₂ (uncurry-proof arg1) (uncurry-proof arg2) (uncurry-proof {!!})
uncurry-proof (⇓app (⇓app {f = fun (app f f₁)} x arg2 y) arg1 eval)     = ⇓app (⇓app (uncurry-proof x) (uncurry-proof arg2) (uncurry-proof y)) (uncurry-proof arg1) (uncurry-proof eval)
uncurry-proof (⇓app (⇓app {f = fun (app₂ f f₁ f₂)} x arg2 y) arg1 eval) = ⇓app (⇓app (uncurry-proof x) (uncurry-proof arg2) (uncurry-proof y)) (uncurry-proof arg1) (uncurry-proof eval)
uncurry-proof (⇓app l@(⇓app {f = app f arg3} x arg2 y) arg1 eval)       = ⇓app (uncurry-proof l) (uncurry-proof arg1) (uncurry-proof eval)
uncurry-proof (⇓app (⇓app {f = app₂ f f₁ f₂} x arg2 y) arg1 eval)       = ⇓app (⇓app (uncurry-proof x) (uncurry-proof arg2) (uncurry-proof y)) (uncurry-proof arg1) (uncurry-proof eval)
uncurry-proof (⇓app clos arg eval)                                      = {!!}
uncurry-proof (⇓app₂ clos arg1 arg2 eval)                               = ⇓app₂ (uncurry-proof clos) (uncurry-proof arg1) (uncurry-proof arg2) (uncurry-proof eval)
