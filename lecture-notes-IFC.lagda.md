File structure:

- [`LambdaSec/Utils.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/Utils.agda)
  Helper lemmas
- [`LambdaSec/LabelLattice.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/LabelLattice.agda)
  The abstract interface for security labels.
- [`LambdaSec/TwoPointLattice.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/TwoPointLattice.agda)
  The concrete two-point lattice with `low` and `high`.
- [`LambdaSec/LambdaSec.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/LambdaSec.agda)
  The IFC calculus: its syntax, type system, and big-step semantics.
- [`LambdaSec/LogicalRelations.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/LogicalRelations.agda)
  The security logical relations and the fundamental theorem.
- [`LambdaSec/Erasure.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/Erasure.agda)
  LambdaSec simulates with erased LambdaSec.
- [`LambdaSec/Noninterference.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/Noninterference.agda)
  The top-level statement of noninterference together with the two instantiations,
  one using logical relations and the other using erasure-based simulation.

```
{-# OPTIONS --rewriting #-}

open import LambdaSec.Noninterference public
```
