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
    v v₀ v₁ : Val
    p q r s : (Γ ⊢ t)

-- TODO: NEED TO BE PROVEN PROPERLY
--postulate
--  clos-eq :
--          γ ⊢ q ↓ v₀
--        → γ ⊢ (ref-curry q) ↓ v₁
--        → v₁ ≡ v₀


data _≡v_ (x : Val) : Val → Set where
  refl : x ≡v x

postulate
  clos-eq : {v1 v2 : Val}
          → v1 ≡ v2
          → (v1 `∷ γ) ⊢ p ↓ v₀
          → (v2 `∷ γ) ⊢ p ↓ v₀
          → (closV γ p) ≡v (closV γ q)

tup-eq : ∀ {x y a b} → x ≡v a → y ≡v b → (tupV x y) ≡v (tupV a b)
tup-eq refl refl = refl


f : Val → Val
f unitV = unitV
f (numV x) = (numV x)
f (tupV x x₁) = tupV (f x) (f x₁)
f (closV x x₁) = closV x (ref-curry x₁)
f (closV₂ x x₁) = closV₂ x (ref-curry x₁)

val-eq : γ ⊢ q ↓ v → γ ⊢ (ref-curry q) ↓ (f v)
val-eq (↓var x) = {!!}
val-eq ↓num = ↓num
val-eq (↓tup x x₁) = ↓tup (val-eq x) (val-eq x₁)
val-eq (↓add x x₁) = ↓add (val-eq x) (val-eq x₁)
val-eq (↓fst x) = ↓fst (val-eq x)
val-eq (↓snd x) = ↓snd (val-eq x)
val-eq ↓fun = ↓fun
val-eq ↓fun₂ = ↓fun₂
val-eq (↓app x x₁ x₂) = ↓app (val-eq x) x₁ (val-eq x₂)
val-eq (↓app₂ {f = fst f₁} clos arg1 arg2 eval) = {!!}
val-eq (↓app₂ {f = snd f₁} clos arg1 arg2 eval) = {!!}
val-eq (↓app₂ {f = var x} clos arg1 arg2 eval) = {!!}
val-eq (↓app₂ {f = fun₂ f₁} clos arg1 arg2 eval) = ↓app (↓app {!!} arg2 (val-eq {!!})) arg1 (val-eq eval)
val-eq (↓app₂ {f = app f₁ f₂} clos arg1 arg2 eval) = ↓app₂ (val-eq clos) arg1 arg2 (val-eq eval)
val-eq (↓app₂ {f = app₂ f₁ f₂ f₃} clos arg1 arg2 eval) = ↓app₂ (val-eq clos) arg1 arg2 (val-eq eval)

-- curry-semantics-proof : ∅ ⊢ p ↓ v → ∅ ⊢ (ref-curry p) ↓ v
sem-eq : γ ⊢ q ↓ v₀ → γ ⊢ (ref-curry q) ↓ v₁ → v₁ ≡v v₀
sem-eq x = {!!}
