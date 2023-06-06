open import Data.List.Base
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s; _+_)
open import Language

private
  variable
    Γ : Ctx
    t u v p : Ty

pair-var : (t ∷ u ∷ Γ) ⊢ p → ((tupT t u) ∷ Γ) ⊢ p
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

ref-uncurry : Γ ⊢ t → Γ ⊢ t
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

env-help : (t ∷ u ∷ Γ) ⊢ p → (u ∷ Γ) ⊢ p
env-help unit = unit
env-help (num x) = num x
env-help (x , x₁) = env-help x , env-help x₁
env-help (add x x₁) = add (env-help x) (env-help x₁)
env-help (fst x) = fst (env-help x)
env-help (snd x) = snd (env-help x)
env-help (var here) = {!!}
env-help (var (there x)) = var x
env-help (fun x) = {!!}
env-help (app x x₁) = app (env-help x) (env-help x₁)

explode-tuple : ((tupT t u) ∷ Γ) ⊢ p → (t ∷ u ∷ Γ) ⊢ p
explode-tuple unit = unit
explode-tuple (num x) = num x
explode-tuple (x , x₁) = explode-tuple x , explode-tuple x₁
explode-tuple (add x x₁) = explode-tuple x₁
explode-tuple (fst (var here)) = var here
explode-tuple (snd (var here)) = var (there here)
explode-tuple (var here) = {!!}
explode-tuple (var (there x)) = var (there (there x))
explode-tuple (fst x) = fst (explode-tuple x)
explode-tuple (snd x) = snd (explode-tuple x)
explode-tuple (fun x) = {!!}
explode-tuple (app x x₁) = app (explode-tuple x) (explode-tuple x₁)

ref-curry : Γ ⊢ t → Γ ⊢ t
ref-curry unit = unit
ref-curry (num x) = num x
ref-curry (x , x₁) = ref-curry x , ref-curry x₁
ref-curry (add x x₁) = add (ref-curry x) (ref-curry x₁)
ref-curry (fst x) = fst (ref-curry x)
ref-curry (snd x) = snd (ref-curry x)
ref-curry (var x) = var x
ref-curry (fun x) = fun x
ref-curry (app x x₁) = app x x₁
