import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.List.Base
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Language
open import Refactoring2


-- EX 1 (basic arithmetic)
ex1 : [] ⊢ numT
ex1 = add (num 1) (num 2)

v1 : Val
v1 = numV 3

↓ex1 : ∅ ⊢ ex1 ↓ v1
↓ex1 = ↓add ↓num ↓num

-- EX 2 (basic function application)
ex2 : [] ⊢ numT
ex2 = (app (fun (add (num 1) (var here))) (num 2))

v2 : Val
v2 = numV 3

↓ex2 : ∅ ⊢ ex2 ↓ v2
↓ex2 = ↓app ↓fun ↓num (↓add ↓num (↓var here))

-- EX 3 (curried function)
ex3 : [] ⊢ numT
ex3 = app (app (fun (fun (add (var here) (var (there here)) ))) (num 4)) (num 2)

v3 : Val
v3 = numV 6

↓ex3 : ∅ ⊢ ex3 ↓ v3
↓ex3 = ↓app (↓app ↓fun ↓num ↓fun) ↓num (↓add (↓var here) (↓var (there here)))

-- EX 4 (basic tuple)
ex4 : [] ⊢ numT
ex4 = snd ((num 4) , (num 5))

v4 : Val
v4 = (numV 5)

↓ex4 : ∅ ⊢ ex4 ↓ v4
↓ex4 = ↓snd (↓tup ↓num ↓num)

-- EX 5 (function with tuple)
ex5 : [] ⊢ numT
ex5 = app (fun (add (fst (var here)) (snd (var here)))) ((num 21) , (num 37))

v5 : Val
v5 = numV 58

↓ex5 : ∅ ⊢ ex5 ↓ v5
↓ex5 = ↓app ↓fun (↓tup ↓num ↓num) (↓add (↓fst (↓var here)) (↓snd (↓var here)))

-- EX 6 (nested mixed type tuples)
ex6 : [] ⊢ tupT (tupT numT numT) numT
ex6 = (((num 3) , (num 4)) ,  (num 6) )

-- EX 7 (higher order functions)
ex7 : [] ⊢ numT
ex7 = app (fun (add (add (app (var here) (num 1)) (app (var here) (num 4))) (app (var here) (num 9)))) (app (fun (fun (add (var here) (var (there here))))) (num 5))

v7 : Val
v7 = numV 29

↓ex7 : ∅ ⊢ ex7 ↓ v7
↓ex7 = ↓app ↓fun (↓app ↓fun ↓num ↓fun) (↓add (↓add (↓app (↓var here) ↓num (↓add (↓var here) (↓var (there here)))) (↓app (↓var here) ↓num (↓add (↓var here) (↓var (there here))))) (↓app (↓var here) ↓num (↓add (↓var here) (↓var (there here)))))

-- EX 8 (multi-arg functions)
ex8 : [] ⊢ numT
ex8 = app₂ (fun₂ (add (var here) (var (there here)))) (num 5) (num 9)

v8 : Val
v8 = numV 14

↓ex8 : ∅ ⊢ ex8 ↓ v8
↓ex8 = ↓app₂ ↓fun₂ ↓num ↓num (↓add (↓var here) (↓var (there here)))

↓ex8₁ : ∅ ⊢ (ref-curry ex8) ↓ v8
↓ex8₁ = ↓app (↓app ↓fun ↓num ↓fun) ↓num (↓add (↓var here) (↓var (there here)))

-- EX 9 (long application chain)

ex9 : [] ⊢ numT
ex9 = app (app (app (app (fun (fun (fun (fun (add (add (var here) (var (there here))) (add (var (there (there here))) (var (there (there (there here))))))))))  (num 4)) (num 3)) (num 2)) (num 1)

v9 : Val
v9 = numV 10

-- EX 10
ex10 : [] ⊢ numT ⇒ numT
ex10 = fun (app₂ (fun₂ (add (var here) (var (there here)))) (num 5) (num 9))

v10 : Val
v10 = closV {t = numT} ∅
        (app (app (fun (fun (add (var here) (var (there here))))) (num 9))
         (num 5))

v10₁ : Val
v10₁ = closV {t = numT} ∅
         (app₂ (fun₂ (add (var here) (var (there here)))) (num 5) (num 9))

↓ex10 : ∅ ⊢ (ex10) ↓ v10₁
↓ex10 = ↓fun
