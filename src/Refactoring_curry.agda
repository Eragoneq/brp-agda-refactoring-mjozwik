open import Data.List.Base
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; _+_)
open import Language

private
  variable
    Γ : Ctx
    t u v p : Ty

ref-type : Ty → Ty
ref-type unitT         = unitT
ref-type numT          = numT
ref-type (tupT x x₁)   = tupT (ref-type x) (ref-type x₁)
ref-type (x ⇒ x₁)      = (ref-type x) ⇒ (ref-type x₁)
ref-type (/ t / u ⇒ v) = (ref-type u) ⇒ (ref-type t) ⇒ (ref-type v)

ref-ctx : Ctx → Ctx
ref-ctx []             = []
ref-ctx (x ∷ x₁)       = (ref-type x) ∷ (ref-ctx x₁)

ref-lookup : t ∈ Γ → (ref-type t) ∈ (ref-ctx Γ)
ref-lookup here        = here
ref-lookup (there x)   = there (ref-lookup x)

ref-curry : Γ ⊢ p → (ref-ctx Γ) ⊢ (ref-type p)
ref-curry unit         = unit
ref-curry (num x)      = num x
ref-curry (x , x₁)     = (ref-curry x) , (ref-curry x₁)
ref-curry (add x x₁)   = add (ref-curry x) (ref-curry x₁)
ref-curry (fst x)      = fst (ref-curry x)
ref-curry (snd x)      = snd (ref-curry x)
ref-curry (var x)      = var (ref-lookup x)
ref-curry (fun x)      = fun (ref-curry x)
ref-curry (fun₂ x)     = fun (fun (ref-curry x))
ref-curry (app x arg)  = app (ref-curry x) (ref-curry arg)
ref-curry (app₂ x y z) = app (app (ref-curry x) (ref-curry z)) (ref-curry y)
