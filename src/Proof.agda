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

-- TODO: NEED TO BE PROVEN PROPERLY
--postulate
--  clos-eq :
--          γ ⊢ q ↓ v₀
--        → γ ⊢ (ref-curry q) ↓ v₁
--        → v₁ ≡ v₀


--data _≡v_ (x : Val) : Val → Set where
--  refl : x ≡v x

--tup-eq : ∀ {x y a b} → x ≡v a → y ≡v b → (tupV x y) ≡v (tupV a b)
--tup-eq refl refl = refl

ref-env : Env Γ → Env Γ
ref-val : Val t → Val t

ref-env []       = []
ref-env (v ∷ vs) = (ref-val v) ∷ (ref-env vs)

ref-val unitV         = unitV
ref-val (numV x)      = numV x
ref-val (tupV x x₁)   = tupV (ref-val x) (ref-val x₁)
ref-val (closV x x₁)  = closV (ref-env x) (ref-curry x₁)
ref-val (closV₂ x x₁) = closV₂ (ref-env x) (ref-curry x₁)

lp : (γ : Env Γ) → (x : t ∈ Γ) → lookup-val (ref-env γ) x ≡ ref-val (lookup-val γ x)
lp (x ∷ xs) here = refl
lp (x ∷ xs) (there y) = lp xs y

convert : ∀ {f b} → (γ ⊢ fun₂ f ↓ closV₂ δ b) → ((ref-env γ) ⊢ fun (fun f) ↓ closV (ref-env δ) (fun (ref-curry b)))
convert x = {!!}

val-eq : γ ⊢ q ↓ v → (ref-env γ) ⊢ (ref-curry q) ↓ (ref-val v)
val-eq {γ = γ} (↓var x) = subst (λ y → _ ⊢ _ ↓ y) (lp γ x) (↓var x)
val-eq ↓num = ↓num
val-eq (↓tup x x₁) = ↓tup (val-eq x) (val-eq x₁)
val-eq (↓add x x₁) = ↓add (val-eq x) (val-eq x₁)
val-eq (↓fst x) = ↓fst (val-eq x)
val-eq (↓snd x) = ↓snd (val-eq x)
val-eq (↓fun) = ↓fun
val-eq ↓fun₂ = ↓fun₂
val-eq (↓app x x₁ x₂) = ↓app (val-eq x) (val-eq x₁) (val-eq x₂)
val-eq (↓app₂ {f = fun₂ f₁} clos arg1 arg2 eval) = ↓app (↓app {!!} (val-eq arg2) ↓fun) (val-eq arg1) (val-eq eval)
val-eq (↓app₂ {f = fst x} clos arg1 arg2 eval) = ↓app₂ (val-eq clos) (val-eq arg1) (val-eq arg2) (val-eq eval)
val-eq (↓app₂ {f = snd x} clos arg1 arg2 eval) = ↓app₂ (val-eq clos) (val-eq arg1) (val-eq arg2) (val-eq eval)
val-eq (↓app₂ {f = var x} clos arg1 arg2 eval) = ↓app₂ (val-eq clos) (val-eq arg1) (val-eq arg2) (val-eq eval)
val-eq (↓app₂ {f = app x y} clos arg1 arg2 eval) = ↓app₂ (val-eq clos) (val-eq arg1) (val-eq arg2) (val-eq eval)
val-eq (↓app₂ {f = app₂ x y z} clos arg1 arg2 eval) = ↓app₂ (val-eq clos) (val-eq arg1) (val-eq arg2) (val-eq eval)

