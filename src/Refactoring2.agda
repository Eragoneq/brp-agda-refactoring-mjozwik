open import Data.List.Base
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; _+_)
open import Language

private
  variable
    Γ : Ctx
    t u v p : Ty

ref-uncurry : Γ ⊢ p → Γ ⊢ p
ref-uncurry unit = unit
ref-uncurry (num x) = num x
ref-uncurry (x , x₁) = (ref-uncurry x) , (ref-uncurry x₁)
ref-uncurry (add x x₁) = add (ref-uncurry x) (ref-uncurry x₁)
ref-uncurry (fst x) = fst (ref-uncurry x)
ref-uncurry (snd x) = snd (ref-uncurry x)
ref-uncurry (var x) = var x
ref-uncurry (fun x) = fun (ref-uncurry x)
ref-uncurry (fun₂ x) = fun₂ (ref-uncurry x)
ref-uncurry (app (app (fun (fun x)) arg2) arg1) = app₂ (fun₂ (ref-uncurry x)) (ref-uncurry arg1) (ref-uncurry arg2)
ref-uncurry (app x arg) = app (ref-uncurry x) (ref-uncurry arg)
ref-uncurry (app₂ x x₁ x₂) = app₂ (ref-uncurry x) (ref-uncurry x₁) (ref-uncurry x₂)


-- ex1 : [] ⊢ numT
-- ex1 = app (app (fun (fun (add (var here) (var (there here))))) (num 5)) (num 9)

-- ex2 : [] ⊢ numT
-- ex2 = ref-curry ex1

ref-type : Ty → Ty
ref-type unitT = unitT
ref-type numT = numT
ref-type (tupT x x₁) = tupT (ref-type x) (ref-type x₁)
ref-type (x ⇒ x₁) = (ref-type x) ⇒ (ref-type x₁)
ref-type (/ t / u ⇒ v) = (ref-type u) ⇒ (ref-type t) ⇒ (ref-type v)

ref-ctx : Ctx → Ctx
ref-ctx [] = []
ref-ctx (x ∷ x₁) = (ref-type x) ∷ (ref-ctx x₁)

ref-lookup : t ∈ Γ → (ref-type t) ∈ (ref-ctx Γ)
ref-lookup here = here
ref-lookup (there x) = there (ref-lookup x)

ref-curry : Γ ⊢ p → (ref-ctx Γ) ⊢ (ref-type p)
ref-curry unit = unit
ref-curry (num x) = num x
ref-curry (x , x₁) = (ref-curry x) , (ref-curry x₁)
ref-curry (add x x₁) = add (ref-curry x) (ref-curry x₁)
ref-curry (fst x) = fst (ref-curry x)
ref-curry (snd x) = snd (ref-curry x)
ref-curry (var x) = var (ref-lookup x)
ref-curry (fun x) = fun (ref-curry x)
ref-curry (fun₂ x) = fun (fun (ref-curry x))
ref-curry (app x arg) = app (ref-curry x) (ref-curry arg)
ref-curry (app₂ x y z) = app (app (ref-curry x) (ref-curry z)) (ref-curry y)

-- ex3 : [] ⊢ numT
-- ex3 = ref-uncurry ex2

-- curry : Γ ⊢ (u ⇒ t ⇒ p) → Γ ⊢ (/ t / u ⇒ p)
-- curry (fun (fun x)) = fun₂ x
-- curry x = {!!}
