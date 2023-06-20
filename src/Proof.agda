open import Language
open import Refactoring2
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

private
  variable
    Γ Δ Β : Ctx
    γ : Env Γ
    δ : Env Δ
    β : Env Β
    t u w : Ty
    v : Val t
    p q r s : (Γ ⊢ t)

ref-env : Env Γ → Env (ref-ctx Γ)
ref-val : Val t → Val (ref-type t)

ref-env []       = []
ref-env (v ∷ vs) = (ref-val v) ∷ (ref-env vs)

ref-val unitV         = unitV
ref-val (numV x)      = numV x
ref-val (tupV x x₁)   = tupV (ref-val x) (ref-val x₁)
ref-val (closV x x₁)  = closV (ref-env x) (ref-curry x₁)
ref-val (closV₂ x x₁) = closV (ref-env x) (fun (ref-curry x₁))

lp : (γ : Env Γ) → (x : t ∈ Γ) → lookup-val (ref-env γ) (ref-lookup x) ≡ ref-val (lookup-val γ x)
lp (x ∷ xs) here = refl
lp (x ∷ xs) (there y) = lp xs y

val-eq : γ ⊢ q ↓ v → (ref-env γ) ⊢ (ref-curry q) ↓ (ref-val v)
val-eq {γ = γ} v@(↓var x) = subst (λ x₁ → _ ⊢ _ ↓ x₁) (lp γ x) (↓var (ref-lookup x))
val-eq ↓num = ↓num
val-eq (↓tup x x₁) = ↓tup (val-eq x) (val-eq x₁)
val-eq (↓add x x₁) = ↓add (val-eq x) (val-eq x₁)
val-eq (↓fst x) = ↓fst (val-eq x)
val-eq (↓snd x) = ↓snd (val-eq x)
val-eq (↓fun) = ↓fun
val-eq ↓fun₂ = ↓fun
val-eq (↓app x x₁ x₂) = ↓app (val-eq x) (val-eq x₁) (val-eq x₂)
val-eq (↓app₂ clos arg1 arg2 eval) = ↓app (↓app (val-eq clos) (val-eq arg2) ↓fun) (val-eq arg1) (val-eq eval)
