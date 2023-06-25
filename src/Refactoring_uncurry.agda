open import Data.List.Base
open import Language

private
  variable
    Γ : Ctx
    t u v p : Ty

ref-uncurry : Γ ⊢ p → Γ ⊢ p
ref-uncurry unit                                   = unit
ref-uncurry (num x)                                = num x
ref-uncurry (x , x₁)                               = (ref-uncurry x) , (ref-uncurry x₁)
ref-uncurry (add x x₁)                             = add (ref-uncurry x) (ref-uncurry x₁)
ref-uncurry (fst x)                                = fst (ref-uncurry x)
ref-uncurry (snd x)                                = snd (ref-uncurry x)
ref-uncurry (var x)                                = var x
ref-uncurry (fun x)                                = fun (ref-uncurry x)
ref-uncurry (fun₂ x)                               = fun₂ (ref-uncurry x)
ref-uncurry (app (app (fun (fun x)) arg2) arg1)    = app₂ (fun₂ (ref-uncurry x)) (ref-uncurry arg1) (ref-uncurry arg2)
ref-uncurry (app f arg)                            = app (ref-uncurry f) (ref-uncurry arg)
ref-uncurry (app₂ x x₁ x₂)                         = app₂ (ref-uncurry x) (ref-uncurry x₁) (ref-uncurry x₂)
