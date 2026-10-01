# Categories in anima contexts

The chapter uses distinct copies of the preceding theory. Its constructions
are parameterized by those copies and by the specified changes between them.
The absolute context and the terminal anima context are compared by
equivalences, not by an Agda computation rule.

## Categories in context

1. [Contexts](Section01/Contexts.lagda.md) supplies the contexts, their theory
   copies, and extension by a local anima.
2. [Core](Section01/Core.lagda.md), [Coherence](Section01/Coherence.lagda.md),
   and [PrimitivePreservation](Section01/PrimitivePreservation.lagda.md)
   successively supply the underlying weak change, its operation comparisons,
   and preservation of the selected basic witnesses.
3. [Changes](Section01/Changes.lagda.md) indexes these data and their lifts to
   further anima contexts. [Theory](Theory.lagda.md) and [Axioms](Axioms.lagda.md)
   supply the local constructor and axiom packages.
4. The [functor-expression interpreter](Section01/Expressions/Functors.lagda.md)
   recursively constructs expression comparisons. The corresponding
   [identification comparison](Section01/Expressions/IdentificationComparison.lagda.md)
   and [witness normalization](Section01/Expressions/Witnesses.lagda.md)
   perform the next two steps. The supporting square and boundary calculations
   are in `Section01/ComparisonCalculus/`.
5. [Preservation](Preservation.lagda.md) and
   [AxiomPreservation](AxiomPreservation.lagda.md) collect the constructor
   comparisons currently recorded. These interfaces remain partial. In
   particular, some supplied squares for compound expressions still need to
   be identified with their recursive comparisons. Successive second-level
   normalization still requires compatibility of its selected boundary
   comparisons.
6. [TerminalPreservation](Section01/TerminalPreservation.lagda.md) compares
   the selected terminal universal-property certificate on canonical weakened
   inputs. Its comparison of the terminal identification is the inverse
   comparison from that certificate.

## Dependent products and sums

Read [DependentProducts](Section02/DependentProducts.lagda.md) and
[DependentSums](Section02/DependentSums.lagda.md) for the primitive rules,
then [ProductFunctoriality](Section02/ProductFunctoriality.lagda.md) and
[SumFunctoriality](Section02/SumFunctoriality.lagda.md) for the derived actions.
The whole mapping-anima equivalences are proved in
[ProductMapping](Section02/ProductMapping.lagda.md) and
[SumMapping](Section02/SumMapping.lagda.md).

[SumIdentifications](Section02/MappingCalculus/SumIdentifications.lagda.md)
computes the chosen reflected identifications, their composition and unit
laws, and naturality of the extension computation.
[SumPostcomposition](Section02/MappingCalculus/SumPostcomposition.lagda.md)
proves naturality of the restriction comparisons, retaining their specified
identifications.
[SumComposition](Section02/MappingCalculus/SumComposition.lagda.md) then
proves naturality of the chosen composition comparison separately in both
local functors by computing its restriction and reflecting the resulting squares.
[SumCones](Section02/SumCones.lagda.md) extends whole cones on weakened
absolute cospans and computes their restriction, including the matching.
It also lifts cone comparisons; no computation of the lifted compatibility
witness at the next level is asserted.

[Frobenius](Section02/Frobenius.lagda.md) constructs the equivalence, and
[FrobeniusComparison](Section02/FrobeniusComparison.lagda.md) identifies its
specified components. [ProductPullbacks](Section02/ProductPullbacks.lagda.md)
proves preservation of pullbacks by the primitive dependent product. Its
proof uses the full cone, including its matching identification; the
supporting calculations are in `Section02/ProductCalculus/`. This theorem
has Chapter 5's dependent-product hypothesis.

## Categories over the base and substitution

[GenericPoint](Section03/GenericPoint.lagda.md) constructs the projection and
generic point. [GenericFiber](Section03/GenericFiber.lagda.md) constructs the
two recovery maps, whose equivalence is the axiom in
[Recovery](Section03/Recovery.lagda.md).
[PairPullbacks](Section03/PairPullbacks.lagda.md) proves that the specified
pair square is cartesian, and that dependent sum reflects equivalences.
[RecoverEquivalence](Section03/RecoverEquivalence.lagda.md) proves that
generic fibers detect equivalences, including a criterion stated directly
using a generic-point pullback square.
[SumPullbacks](Section03/SumPullbacks.lagda.md) proves that the total cone
constructed by extension is a pullback. Its legs are the specified sum
functors. Identifying its reflected matching with the separate formula
using the sum compositor and congruence is proved in
[SumConeMatching](Section02/MappingCalculus/SumConeMatching.lagda.md).
Thus `direct-square-isPullback` proves preservation for that precise formula.
[LocalMappingOverBase](Section03/LocalMappingOverBase.lagda.md) compares whole
mapping animae; identification of its chosen relative triangle with the
earlier projection-naturality witness is still open.

[ConstantFamilies](Section03/ConstantFamilies.lagda.md),
[TerminalContext](Section03/TerminalContext.lagda.md), and
[TerminalConstants](Section03/TerminalConstants.lagda.md) give the constant
and terminal-context comparisons.
[Sections](Section03/Sections.lagda.md) constructs the section equivalence
and the section of a local term, retaining the remaining comparison issue.
[FixedShapeInheritance](Section03/FixedShapeInheritance.lagda.md) is an
absolute theorem over an arbitrary base category. It compares pullbacks
using the given naturality and constant-diagram identifications.

[Substitution](Section04/Substitution.lagda.md) supplies a primitive change
for a map of animae, with its constant-family and generic-point comparisons.
[SubstitutionTotals](Section04/SubstitutionTotals.lagda.md) identifies its
total category with the absolute pullback.
Its preservation hypothesis is the restricted interface in
[PullbackChanges](PullbackChanges.lagda.md).
[SuccessiveSubstitutions](Section04/SuccessiveSubstitutions.lagda.md) gives
the category equivalences for successive substitutions; their full
naturality and higher witness comparisons remain to be constructed.
[Quantification](Section04/Quantification.lagda.md) displays the scope of
diagrams after arbitrary further anima substitutions.

## Coverage boundary

The canonical sources are a partial formalization of the chapter. The
remaining results include the named relative-triangle comparison,
forward preservation of animae,
iterated-context comparisons, the relative-isomorphism formula, and the
substituted-section exercise. The first three exercises have implementations
in Section 5. The complete preservation scheme and higher substitution-route
comparisons also remain unfinished.
No missing theorem is supplied as a postulate or by an unresolved Agda hole.
