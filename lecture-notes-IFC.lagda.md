# Learning Goals

+ Programming language-based information-flow control
  using a static type system
+ The statement of the main security guarantee,
  namely noninterference
+ A case study of the proof techniques we've learned:
  logical relations and simulation

# Explicit and Implicit Information Flows

```text

            +-------------+
 Input ===> | Program (P) | ===> Output
 [high]     +-------------+      [low]

```

Suppose input is private (high-security) and output is publicly visible (low-security).

Can we infer input from output (suppose `neg` is boolean negation)?

```text
P₁ = output (neg input)                      -- explicit flow

P₂ = output (if input then false else true)  -- implicit flow
```

Implicit flow: input influences output through *branching*

# Information-Flow Control

Programming language-based information-flow control

+ Information-flow control (IFC) ensures that information transfers adhere to a security policy.
+ In our example, high input must not influence ("flow into") low output.
+ Static IFC using a type system (static analysis)

Types are annotated with security labels (for example, low and high).
Subtyping: low value can flow into a function that expects high (`low ⊑ high`)
but not the other way around (`high ⋤ low`).

The IFC type system rejects illegal explicit flow:

```text
priv-input : Unit -> Bool of high
output     : Bool of low -> Unit

let input = priv-input () in
  output (neg input)
```

The program is ill-typed, because `(neg input) : Bool of high`
but `output` expects `Bool of low`, `high ⋤ low`.

The IFC type system also rejects illegal implicit flow:

```text
priv-input : Unit -> Bool of high
output     : Bool of low -> Unit

let input = priv-input () in
  output (if input then false else true)
```

The program is also ill-typed. The branch condition, `input`,
has type `Bool of high`. As a result, the type of the if-expression
`(if input then false else true)` is `Bool of high` despite
the two branches (unannotated constants) being of `Bool of low`.
We're going to define a "stamping" operator that models this implicit flow
from the branch condition to the result of the entire if-expression.
As we've said, `high ⋤ low`, so the call to `output` is ill-typed.

# LambdaSec

We model the notion of "security" (or "privilege levels") by using
a security label lattice, which is essentially a join semilattice
with a bottom element (least restrictive, or the most public in
the case of confidentiality, like the security of the program itself.)

(Look at `LambdaSec/LabelLattice.agda`)

Our LambdaSec mechanization is based on the λSEC calculus in Ch.3 of
Steve Zdancewic's PhD dissertation (Zdancewic 2002). It is based on
call-by-value left-to-right STLC. The type system of λSEC tracks and checks
security labels. The operational semantics also propagates labels,
but that's only for the proof. λSEC is a fully static IFC language,
so the type system itself is responsible for enforcing security.

(Look at `LambdaSec/LambdaSec.agda`)

[Question] Why does a λ-abstraction (or a function type) carry a label?

It may leak information if we branch on a secret and choose the function
to call. Consider this:

```text
output ((if input then (λx. false) else (λx. true)) true)
```

The `T-App` rule is for this same reason (implicit flow through functions).

# Security Guarantee: Noninterference

The main security guarantee of LambdaSec is *noninterference*.
Noninterference says that whatever private input a LambdaSec program takes,
it always produces the same public-visible output.

We state noninterference using a two-point lattice (low and high).

(Look at `LambdaSec/TwoPointLattice`)

We model input using (single) subsitution. Output is the evaluation result.

```text
Theorem (Noninterference). Suppose Bool of high ⊢ M : Bool of low and ∅ ⊢ Vᵢ : Bool of high.
If M [ V₁ ] ⇓ V₁′ and M [ V₂ ] ⇓ V₂′ then V₁′ = V₂′.
```

(Look at `LambdaSec/Noninterference`)

Following Zdancewic's dissertation, we prove noninterference as
a corollary of the fundamental theorem of security logical relations.

(Look at `LambdaSec/LogicalRelations`)

Following Li and Zdancewic 2010, we can also prove noninterference
using the erasure-and-simulation approach. The key idea is to erase
high-security values to opaque (`●`). The simulation relation
is defined using the `erase` function: λSEC term `M` is in sync with
the erased term `Mₑ` if `erase M ζ = Mₑ`.

(Look at `LambdaSec/Simulation`)

# The Agda Mechanization

File structure of the LambdaSec development:

- [`LambdaSec/Utils.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/Utils.agda)
  Helper lemmas
- [`LambdaSec/LabelLattice.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/LabelLattice.agda)
  The abstract interface for security labels.
- [`LambdaSec/TwoPointLattice.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/TwoPointLattice.agda)
  The concrete two-point lattice with `low` and `high`.
- [`LambdaSec/LambdaSec.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/LambdaSec.agda)
  The IFC calculus: its syntax, type system, and big-step semantics. Intrinsically-typed terms, PLFA style
- [`LambdaSec/LogicalRelations.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/LogicalRelations.agda)
  The security logical relations and the fundamental theorem.
- [`LambdaSec/Simulation.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/Simulation.agda)
  LambdaSec simulates with erased LambdaSec.
- [`LambdaSec/Noninterference.agda`](https://github.com/jsiek/PLFA-Spring-2026/blob/main/LambdaSec/Noninterference.agda)
  The top-level statement of noninterference together with the two instantiations,
  one using logical relations and the other using erasure-based simulation.

```
{-# OPTIONS --rewriting #-}

open import LambdaSec.Noninterference public
  using ( noninterference-LR     -- proof of NI using logical relations
        ; noninterference-sim    -- proof of NI using erasure and simulation
  )
```

# References

1. Expressing Information Flow Properties. Kozyri, Chong, and Myers. 2021
2. Programming Languages for Information Security. Zdancewic. 2002
3. Arrows for Secure Information Flow. Li and Zdancewic. 2010
