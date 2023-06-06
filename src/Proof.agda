open import Language
open import Refactoring2
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

private
  variable
    Γ : Ctx
    γ : Env Γ
    t u : Ty
    v : Val
    p : (Γ ⊢ t)

curry-semantics-proof : ∅ ⊢ p ↓ v → ∅ ⊢ (ref-curry p) ↓ v
curry-semantics-proof ↓num = ↓num
curry-semantics-proof (↓tup x x₁) = ↓tup (curry-semantics-proof x) (curry-semantics-proof x₁)
curry-semantics-proof (↓add x x₁) = ↓add (curry-semantics-proof x) (curry-semantics-proof x₁)
curry-semantics-proof (↓fst x) = ↓fst (curry-semantics-proof x)
curry-semantics-proof (↓snd x) = ↓snd (curry-semantics-proof x)
curry-semantics-proof ↓fun = {!!}
curry-semantics-proof ↓fun₂ = {!!}
curry-semantics-proof (↓app x x₁ x₂) = ↓app (curry-semantics-proof x) x₁ x₂
curry-semantics-proof (↓app₂ x x₁ x₂ x₃) = {!!}
