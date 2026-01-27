<!-- # B629 Mechanized Proofs for PL Metatheory -->

**Indiana University, Spring 2026**

In this course we learn how to write mechanized proofs in Agda of
theorems about programming languages. The course will use the online
textbook [Programming Language Foundations in Agda](https://plfa.github.io/)
(PLFA).

[Agda](https://agda.readthedocs.io/en/latest/index.html) is a proof
assistant and a dependently typed language.  No prior knowledge of
Agda is assumed; it will be taught from scratch.  Prior knowledge of
another proof assistant or dependently typed language is helpful but
not necessary.


## Instructor

Prof. Jeremy Siek, Luddy 3016, [jsiek@iu.edu](mailto:jsiek@iu.edu)


## Lectures

Tuesday and Thursday at 2:20-3:35pm in Wylie Hall (WY) Room 101.


## Office Hours (in Luddy Hall 3016 or the neighboring 3014)

* TBD


## Assignments (tentative)

1. January 20, Exercises `Bin` (in [Naturals](https://plfa.github.io/Naturals/)) and
  `Bin-laws` (in [Induction](https://plfa.github.io/Induction/)).
  
2. January 27, Exercises `Bin-predicates` (in [Relations](https://plfa.github.io/Relations/)) and
  `Bin-embedding` (in [Isomorphism](https://plfa.github.io/Isomorphism/)).

3. Exercises
   `⊎-weak-×` (in [Connectives](https://plfa.github.io/Connectives/)), 
   `⊎-dual-×` (in [Negation](https://plfa.github.io/Negation/)),
   `∃-distrib-⊎`,
   `∃¬-implies-¬∀`,
   `Bin-isomorphism` (in [Quantifiers](https://plfa.github.io/Quantifiers/)).

4. Exercises 
   `_<?_`, 
   `iff-erasure` (in [Decidable](https://plfa.github.io/Decidable/)),
   `foldr-++`,
   `foldr-∷`, and
   `Any-++-⇔` (in [Lists](https://plfa.github.io/Lists/)).

5. Exercises
   `mul`,
   `—↠≲—↠′`, and
   `⊢mul`
   (in [Lambda](https://plfa.github.io/Lambda/)).
   Exercises
   `progress′` and
   `unstuck`
   (in [Properties](https://plfa.github.io/Properties/)).

6. Formalize the STLC using the extrinsic
   style, as in [Lambda](https://plfa.github.io/Lambda/),
   but using de Bruijn indices to represent variables,
   as in [DeBruijn](https://plfa.github.io/DeBruijn/).
   You should use the `ext`, `rename`, `exts`, and `subst`
   functions from the DeBruijn chapter, simplifying the
   type declarations of those functions. For example,

        exts : ∀ {Γ Δ}
          → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
            ---------------------------------
          → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)

   becomes

        exts : 
          → (Var → Term)
            ------------
          → (Var → Term)
        
   where  `Var` is define to just be `ℕ`.
   You will need to prove a type preservation lemma for
   each of `ext`, `rename`, `exts`, and `subst`,
   whose declaration will be analogous to the type 
   declaration of those functions in the DeBruijn chapter.
   For example,
   
        exts-pres : ∀ {Γ Δ σ}
          → (∀ {A x}  →      Γ ∋ x ⦂ A →            Δ ⊢ σ x ⦂ A)
            ----------------------------------------------------
          → (∀ {A B x} → Γ , B ∋ x ⦂ A → Δ , B ⊢ (exts σ) x ⦂ A)

   Prove the analogous theorem to `preserve`
   in [Properties](https://plfa.github.io/Properties/).
   You may omit natural numbers (0, suc, and case) and μ
   from your formalization of the STLC, instead
   including a unit type.

7. Termination and Bidirectional Typing:

    * Extend the termination proof for STLC
      to include products and sums, as they appear
      in Chapter [More](https://plfa.github.io/More/)
      (you may use either approach to products).
      Also, try to add μ and report on where the proof breaks.

    * Extend the bidirectional type rules, `synthesize`, and `inherit`
      to handle products and sums.

8. Do the `variants` exercise in
   [Subtyping and Records](./lecture-notes-Subtyping.lagda.md).

9. Do the `products` exercise in
   [Bisimulation](https://plfa.github.io/Bisimulation/)
   and the `big-alt-implies-multi` exercise
   in [BigStep](https://plfa.github.io/BigStep/).

10. Project Description Due.
    Write 1 page describing your project.  The description should
	include a list of the formal artifacts (definitions, theorems)
	that you plan to turn in.

## Project

Choose a language feature that is not spelled out in PLFA to formalize
and prove type safe in Agda. (If you have a different kind of
project in mind, I'm happy to consider alternatives, so long as it
includes proving some non-trivial property of a programming language.)
Your formalization should include both a static semantics (aka. type
system), a dynamic semantics, and a proof of type safety. For the
dynamic semantics you must use a different style than the approach
used in PLFA, that is, do not use a reduction semantics. Examples of
other styles you can use are

* small-step reduction with evaluation contexts
* big-step semantics
* definitional interpreter (recursive function with gas)
* abstract machine (e.g. CEK)
* virtual machine (CAM)
* denotational semantics
* axiomatic semantics (e.g. Hoare Logic)

Resources:

* The book _Types and Programming Languages_ (TAPL) by Benjamin Pierce
  has many examples of language features that would be an appropriate
  choice for your project.
  
* The book _Semantics Engineering with PLT Redex_ by Felleisen,
  Findler, and Flatt is a good resource for evaluation contexts,
  abstract machines, and
  continuations. The earlier book draft
  [_Programming Languages and Lambda Calculi_](http://www.cs.utah.edu/plt/publications/pllc.pdf) (PLLC) by Felleisen and Flatt covers similar material.

* _The Formal Semantics of Programming Languages_ (FSPL) by Winskel
  includes lots of semantics styles (small-step, big-step, axiomatic,
  denotational), eager and lazy evaluation, nondeterminism and
  parallelism.

* _Practical Foundations for Programming Languages_ (PFPL) by Robert
  Harper includes material on logical relations.

* [Type Safety in Three Easy Lemmas](http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html) is a blog post of mine
  that shows how to prove type safety using a definitional
  interpreter with gas.

* [Type Safety in Five Easy Lemmas](http://siek.blogspot.com/2012/08/type-safety-in-five-easy-lemmas.html) is a blog post of mine
  that shows how to prove type safety using an abstract machine.


Ideas for project language features:

* Lazy evaluation (aka. call-by-need)
  (e.g., see my paper _Improving the lazy Krivine machine_)
* Let polymorphism (extend [TypeInference](./TypeInference.lagda.md))
* Continuations (PLLC)
* Featherweight Java (TAPL Chapter 19)
* Exceptions (TAPL Chapter 14)
* While loops and variable assignment (the IMP language in FSPL)
* Recursive Types (TAPL Chapter 20)
* Nondeterminism
* Parallelism
* Reasoning about program equality using logical relations (PFPL)
* Bounded Quantification (TAPL Chapter 26)
* Higher-Order Polymorphism (TAPL Chapter 30)


## Schedule

| Month    | Day | Topic    | Notes |
| -------- | --- | -------- | ---- |
| January  | 13  | [Naturals](https://plfa.github.io/Naturals/) & [Induction](https://plfa.github.io/Induction/) | [link](./lecture-notes-Naturals-Induction.lagda.md) |
|          | 15  | [Relations](https://plfa.github.io/Relations/) | [link](./lecture-notes-Relations.lagda.md) |
|          | 20  | [Equality](https://plfa.github.io/Equality/) & [Isomorphism](https://plfa.github.io/Isomorphism/) | [link](./lecture-notes-Equality.lagda.md) |
| 	   | 22  | [Connectives](https://plfa.github.io/Connectives/) & [Negation](https://plfa.github.io/Negation/) | [link](./lecture-notes-Connectives.lagda.md) |
|	   | 27  | [Quantifiers](https://plfa.github.io/Quantifiers/) & [Decidable](https://plfa.github.io/Decidable/) |
|          | 29  | [Lists](https://plfa.github.io/Lists/) and higher-order functions |
| February | 3  | [Lambda](https://plfa.github.io/Lambda/) the Simply Typed Lambda Calculus |
|          | 5 | [Properties](https://plfa.github.io/Properties/) such as type safety |
|          | 10 | [DeBruijn](https://plfa.github.io/DeBruijn/) representation of variables |
|          | 12 | [More](https://plfa.github.io/More/) constructs: numbers, let, products (pairs), sums, unit, empty, lists |
|          | 17 | [STLC Termination via Logical Relations](./STLC-Termination.lagda.md) |
|          | 19 | [Inference](https://plfa.github.io/Inference/) bidirectional type inference |
|          | 24 | [Subtyping and Records](./lecture-notes-Subtyping.lagda.md) |
|          | 26  | [Bisimulation](https://plfa.github.io/Bisimulation/) |
|  March   | 3  | [Untyped](https://plfa.github.io/Untyped/) Lambda Calculus |
|          | 5 | [Confluence](https://plfa.github.io/Confluence/) of the Lambda Calculus |
|          | 10 | [BigStep](https://plfa.github.io/BigStep/) Call-by-name Evaluation of the Lambda Calculus |
|          | 12  | Spring Break, no class |
|          | 17  | Spring Break, no class |
|          | 19  | [Denotational](https://plfa.github.io/Denotational/) semantics of the Lambda Calculus |
|          | 24  | [Denotational](https://plfa.github.io/Denotational/) continued, [Recording](https://iu.mediaspace.kaltura.com/media/Lecture+March+30%2C+Denotational+Semantics/1_da4xq013) |
|          | 26  | [Compositional](https://plfa.github.io/Compositional/) |
|          | 31  | [Soundness](https://plfa.github.io/Soundness/), [Recording](https://iu.mediaspace.kaltura.com/media/Lecture+April+6%2C+Soundness+of+reduction+with+respect+to+denotational+semantics/1_o5gwttt7) |
| April    |  2  | [Adequacy](https://plfa.github.io/Adequacy/), [Recording](https://iu.mediaspace.kaltura.com/media/Lecture+April+8%2C+Adequacy+of+Denotational+Semantics+with+respect+to+Operational+Semantics/1_1eoqorgy) |
|          |  7  | [ContextualEquivalence](https://plfa.github.io/ContextualEquivalence/) and [ScottNumeralsPlus](./ScottNumeralsPlus.lagda.md), [Recording](https://iu.mediaspace.kaltura.com/media/Lecture+April+13%2C+Contextual+Equivalence%2C+Addition+of+Scott+Numerals/1_xidyzfa5) |
|          |  9  | [Unification](./Unification.lagda.md), [Recording](https://iu.mediaspace.kaltura.com/media/Lecture+April+15A+Scott+Numerals+continuedB+Unification/1_s9t5bm7r) |
|          | 14  | [Unification](./Unification.lagda.md) continued, [Recording](https://iu.mediaspace.kaltura.com/media/Lecture+April+20A+Unification+continued/1_s965cxmw) |
|          | 16  | [TypeInference](./TypeInference.lagda.md), [Recording](https://iu.mediaspace.kaltura.com/media/Lecture+April+22A+Type+Inference/1_dzkr4hhs) |
|          | 21  | [Gradual Typing](./GradualTyping.lagda.md), [Recording](https://iu.mediaspace.kaltura.com/media/Lecture+April+27A+Gradual+Typing/1_r6ockrxd) |
|          | 23  | [SystemF](./SystemF.lagda.md) Universal Types (aka. parametric polymorphism), [Recording](https://iu.mediaspace.kaltura.com/media/Lecture+April+29A+System+F+%26+Parametric+Polymorphism/1_3warcwd3) |
|          | 28  | TBD
|          | 30  | TBD

