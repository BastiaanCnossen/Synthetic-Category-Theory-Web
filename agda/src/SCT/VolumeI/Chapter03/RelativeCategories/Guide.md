# Categories and functors over a base

Fix functors `f : MAP C S` and `g : MAP D S`. A functor over `S` is a functor
from `C` to `D` with a specified identification of its composite with `g`
and `f`. An identification of two such functors must respect those triangles.
The modules here develop these data and their mapping animae using the
Chapter 1 structures. They do not assume dependent products or Chapter 5's
primitive contextual theories.

## Basic constructions

1. [Functors](Functors.lagda.md) defines `FunctorOver`, identity and composition,
   and the relative functor and mapping categories.
2. [Identifications](Identifications.lagda.md) defines `FunctorOverIso` and
   `FunctorOverIso₂`, composition, inverses, whiskering, and the unit and
   associativity comparisons over the base.
3. [Equivalences](Equivalences.lagda.md) supplies relative inverse data.
4. [Products](Products.lagda.md), [pullbacks](Pullbacks.lagda.md), and
   [coproducts](Coproducts.lagda.md) give the corresponding relative constructions.
5. [The terminal base](TerminalBase.lagda.md) relates this language to the
   absolute one.
6. [Morphisms](Morphisms.lagda.md) defines transformations over the base with
   their normalized comparison to the identity of the structure functor.
   Whiskering, composition, and endpoint changes retain this comparison.
7. [Named morphisms](NamedMorphisms.lagda.md) constructs actual morphisms in
   the relative functor category; [decoded morphisms](DecodedMorphisms.lagda.md)
   gives the reverse construction. These use interval diagrams with full
   relative endpoint comparisons. Their inverse laws and compatibility with
   composition remain open. The underlying expression recovery in
   [MorphismDiagramRecovery](MorphismDiagramRecovery.lagda.md) does not assert
   identification of the witnesses over the base.

## Supporting mathematics

1. `Evaluation/` relates a point of a relative functor or mapping category to
   its explicit functor and triangle, and studies restriction and uncurrying.
2. `IdentificationCalculus/` makes the analogous correspondence for
   identifications, including their higher compatibility witnesses.
   [MappingEquivalence](IdentificationCalculus/MappingEquivalence.lagda.md)
   gives both roundtrip laws. These are fixed-endpoint statements; they do not
   alone establish compatibility with every composition choice.
3. `Composition/` gives precomposition, postcomposition, and jointly
   parameterized composition.
4. `Families/` handles families of relative functors and their identifications.
5. `BaseChange/` studies changing the base, including the projection and
   triangle computations for families.
6. `ConeCalculus/` and `CoproductCalculus/` supply relative universal-property
   arguments with their specified matching witnesses.

The generic cone calculus belongs to Chapter 1 Section 1.6. These relative
modules add the triangles over a base. The distinction matters: agreement of
underlying functors alone does not identify the complete relative diagrams.
