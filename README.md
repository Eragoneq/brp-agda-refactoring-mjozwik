# Formally proving the correctness of the (un)currying refactoring

This repository contains the code used in bachelor thesis project about formally proving correctness of a currying and uncurrying refactoring.
The research project is done for the 2022/2023 edistion of the CSE3000 Research Project at Delft University of Technology.
For this project a simple Haskell-like language (HLL) was created to show a proof-of-concept for the refactoring.

```haskell
-- Original function
f1 : (Int, Int) → Int
f1 (x, y) = x + y

-- Function after currying
f2 : Int → Int → Int
f2 = λ x → (λ y → x + y)
```
An example of the currying refactoring, where uncurrying is the transformation from `f2` back to `f1`.

## Version
This project uses Agda version `2.6.3`, as well as Agda standard library version `1.7.2`.

## Branches
There has been some progress done on the currying which uses tuples instead of special language constructs. 
For anyone interested in continuing the work and implementing it with tuples, this might be a good starting point. 
