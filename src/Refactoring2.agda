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
ref-uncurry (app (app (fun (fun x)) arg2) arg1) = app₂ (fun₂ x) arg1 arg2
ref-uncurry (app x arg) = app (ref-uncurry x) arg
ref-uncurry (app₂ x x₁ x₂) = app₂ (ref-uncurry x) x₁ x₂


-- ex1 : [] ⊢ numT
-- ex1 = app (app (fun (fun (add (var here) (var (there here))))) (num 5)) (num 9)

-- ex2 : [] ⊢ numT
-- ex2 = ref-curry ex1

ref-curry : Γ ⊢ p → Γ ⊢ p
ref-curry unit = unit
ref-curry (num x) = num x
ref-curry (x , x₁) = (ref-curry x) , (ref-curry x₁)
ref-curry (add x x₁) = add (ref-curry x) (ref-curry x₁)
ref-curry (fst x) = fst (ref-curry x)
ref-curry (snd x) = snd (ref-curry x)
ref-curry (var x) = var x
ref-curry (fun x) = fun (ref-curry x)
ref-curry (fun₂ x) = fun₂ (ref-curry x)
ref-curry (app x arg) = app (ref-curry x) arg
ref-curry (app₂ (fun₂ x) x₁ x₂) = app (app (fun (fun x)) x₂) x₁
ref-curry (app₂ x y z) = app₂ (ref-curry x) y z

-- ex3 : [] ⊢ numT
-- ex3 = ref-uncurry ex2

-- curry : Γ ⊢ (u ⇒ t ⇒ p) → Γ ⊢ (/ t / u ⇒ p)
-- curry (fun (fun x)) = fun₂ x
-- curry x = {!!}
