open import Data.List.Base
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; _+_)
open import Language

pair-var : {t u p : Ty} {Γ : Ctx} → (t ∷ u ∷ Γ) ⊢ p → ((tupT t u) ∷ Γ) ⊢ p
pair-var unit = unit
pair-var (num x) = num x
pair-var (x , x₁) = pair-var x , pair-var x₁
pair-var (add x x₁) = add (pair-var x) (pair-var x₁)
pair-var (fst x) = fst (pair-var x)
pair-var (snd x) = snd (pair-var x)
pair-var (var here) = fst (var here)
pair-var (var (there here)) = snd (var here)
pair-var (var (there (there x))) = var (there x)
pair-var (fun x) = {!!}
pair-var (app x x₁) = app (pair-var x) (pair-var x₁)

-- uncurry : {t u o : Ty} {Γ : Ctx} → Γ ⊢ (t ⇒ u ⇒ o) → Γ ⊢ ((tupT t u) ⇒ o)
-- uncurry (fun (fun f)) = fun (pair-var f)
-- uncurry x = {!!}

ref-uncurry : {t : Ty} {Γ : Ctx} → Γ ⊢ t → Γ ⊢ t
ref-uncurry unit = unit
ref-uncurry (num x) = num x
ref-uncurry (x , x₁) = ref-uncurry x , ref-uncurry x₁
ref-uncurry (add x x₁) = add (ref-uncurry x) (ref-uncurry x₁)
ref-uncurry (fst x) = fst (ref-uncurry x)
ref-uncurry (snd x) = snd (ref-uncurry x)
ref-uncurry (var here) = var here
ref-uncurry (var (there here)) = var (there here)
ref-uncurry (var (there (there x))) = var (there (there x))
ref-uncurry (fun x) = fun (ref-uncurry x)
ref-uncurry (app (app (fun (fun f)) arg2) arg1) = app (fun (pair-var f)) (arg1 , arg2)
ref-uncurry (app x arg) = app (ref-uncurry x) arg
