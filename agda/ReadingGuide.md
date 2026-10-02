# Reading the formalization

The chapter and section directories follow the book. Begin with a section's
main mathematical modules; supporting calculations are grouped by subject in
subdirectories. A main module contains the construction or argument itself.
`Everything.agda` is an import aggregate, not a proposed reading order.

## Chapter 1

1. Sections 1.1 and 1.2 introduce the vocabulary and specified coherences.
   Their main modules remain together. `Theory.lagda.md` collects these assumptions.
2. Section 1.3 develops equivalences and products. `ProductCalculus/` and
   `IdentificationCalculus/` contain the parameterized calculations.
   `PairingAssembly` combines coordinate squares using the pairing laws;
   `CoordinateComparisons` and `FramedSubstitution` handle the underlying
   substitution diagrams before any particular product is chosen.
   `CoordinateNaturality` gives the elementary squares, and `Inverses`
   provides cancellation and inverse identities used later for cone matchings.
   `FactorizationCalculus` constructs identities, composites, restrictions,
   inverses and uniqueness of factorizations (`FunctorLift`) together with
   their comparisons; later lifts and functors over a base use it.
   `BinaryFunctorCalculus` treats a functor from a product; the application
   and mapping-composition modules specialize it to evaluation.
3. Section 1.4 develops mapping animae, their core, composition, and detection
   of equivalences. Supporting calculations are in `CompositionCalculus/`,
   `Substitution/`, `ProductCalculus/`, and `SquareCalculus/`.
4. In Section 1.5 start with `Initial`, `Coproducts`, and `Copairing`, followed
   by the coproduct equivalence and associativity proofs.
5. Section 1.6 introduces cones, pullbacks, and embeddings. Its `ConeCalculus/`
   library is reusable in later chapters; `Coordinates/`, `Cospans/`,
   `MappingCalculus/`, `EmbeddingCalculus/`, and `Pasting/` organize the other
   supporting arguments.
6. Sections 1.7 and 1.8 retain the principal functor-category and pushout proofs.
   The calculations involving evaluation, cones, and mapping animae have their
   own supporting folders.

## Chapter 2

1. Start Section 2.1 with `WalkingMorphism`, `Morphisms`, `WalkingTriangle`,
   `TrianglesAndComposites`, and `SquareGluing`. Evaluation and endpoint
   calculations are collected separately.
2. In Section 2.2 read `SegalAxiom`, `Composition`, `ExpressionUnitLaws`,
   `Associativity`, and `ExpressionAssociativity`. These contain the chosen
   composition and its laws, including the endpoint claims. The supporting
   `MorphismCalculus/`, `UnitCalculus/`, `SquareCalculus/`, and
   `EvaluationCalculus/` folders provide the detailed calculations.
   For operations on families of morphisms, read `MorphismCalculus/ExpressionFamilies`
   first: it separates endpoint formulas and their frames from representing
   pullbacks, and constructs composition, endpoint transport, and sections with
   their restriction and parameter-change comparisons.
   `ExpressionFamilyEquivalences` supplies inverse operations and their equations.
   `EndpointFiberOperations` and `EndpointFiberOperationEquivalences` then realize
   these data using endpoint pullbacks. The construction layer needs neither
   pullbacks nor the Segal axiom.
   Here a parameter is a functor `b : MAP Γ B`. An endpoint family gives a
   functor `Γ → C` for each such `b`: for example `F ∘ b` or `G ∘ (F ∘ b)`.
   The family layer retains the difference between the latter and `(G ∘ F) ∘ b`,
   together with the associator comparing them. This is the reason for the
   extra interface; clients can assemble the operation and its laws together.
3. Section 2.3 retains the Rezk axiom, isomorphism embedding, natural
   isomorphisms, and recovery results at its top level. Inverse witnesses and
   composition calculations are grouped underneath it.
4. Sections 2.4 and 2.5 give groupoids and recognition of animae. The
   `ConstantDiagrams/` folder includes both naturality and the exponential law.
5. Section 2.6 contains the hom-composition and elementary Yoneda arguments,
   with supporting endpoint calculations in `HomCalculus/`.

## Chapter 3

1. Sections 3.1–3.4 retain the principal subcategory, localization, and
   geometric-realization results. Lifting, mapping, and cocone calculations
   appear in supporting folders. Subcategories and full subcategories are
   defined by the same square tested on `[1]` and on `One`;
   `Section01/MappingCalculus/TestedInclusions` proves their common
   consequences once for an arbitrary test category.
2. [Relative categories](src/SCT/VolumeI/Chapter03/RelativeCategories/Guide.md)
   is a shared library for categories and functors over a base. It can be used
   independently of the dependent-product assumption.
3. Read Section 3.5 through `DependentProducts`, `DependentProductAction`,
   `DependentProductActionLaws`, `DependentProductUniqueness`,
   `DependentProductsBaseChange`, `DependentProductEmbeddings`, and
   `InternalFunctors`. The corresponding supporting folders are `Currying/`,
   `BaseChange/`, `ProductCalculus/`, and `InternalFunctorCalculus/`.
4. `Section05/PullbackPreservation/` contains partial arguments and conditional
   criteria for the deferred pullback-preservation theorem. Their presence is
   not a claim that this theorem has been proved under Chapter 3 assumptions.
5. In Section 3.6 start with `JoinAxiom`, `Joins`, `JoinMappingOut`,
   `JoinMappingIn`, `CoreOfJoin`, `JoinUnits`, and `TriangleJoins`. General join
   associativity is still open. Different join actions retain their own
   specified comparison witnesses.
6. Section 3.7 contains `Slices`, `RelativeSlices`, and `FunctorsIntoSlices`,
   with the supporting mapping calculations in `MappingCalculus/`.

## Chapter 4

Chapter 4 contains cartesian and cocartesian fibrations, following the current
manuscript order. Begin with `Section01/DirectedPullbacks`, then
`Section02/Lifts`, the slice constructions in Section03, and
`Section04/Adjunctions`. Initial and terminal objects belong to the subsection
`Section04/InitialAndTerminalObjects/` of Adjunctions. Reusable endpoint and
pullback calculations remain grouped beneath their sections.

`Section03/SliceFibrations` proves that ordinary slice projections are
right fibrations, coslice projections are left fibrations, and relative
slice projections have the corresponding property. The proof uses triangle
presentations and Segal pasting with explicit endpoint comparisons; it
does not require functoriality of universals. `HomGroupoids` identifies
slice fibers with hom categories and proves that these are groupoids.

`Section04/AdjointSections` defines adjoint sections and Bousfield
localizations. `AdjunctionCalculus/` contains the normalized component
calculations, section identifications, and inverse-equation arguments.
`InitialAndTerminalObjects/AdjointSections` constructs adjoint sections
from initial and terminal objects. `AdjunctionCharacterization` proves the
converse, and `Contractions` proves the normalized and invertible-component
criteria. Together these cover the four-condition characterization in both
variances. The abstract `SealedTransposition` package exposes the proved
expression operations and inverse laws without expanding their implementations
in downstream proofs.

`HomAdjunctions` constructs the hom-anima equivalence from an adjunction,
including an inverse and both inverse identifications over the base.
Its family operations are supplied by `SealedFamilyTransposition`, with
restriction and parameter-change laws. To see their construction, read
`AdjunctionCalculus/TransposeFamilies`: normalize the input endpoints, apply
transposition, and restore the output endpoints. `TransposeFamilyInverses`
composes the corresponding family equivalences. `ComponentRestriction`
constructs unit and counit sections by restricting the transformations and
transporting their endpoints; their compatibility laws are section fields.
These constructions reuse the Chapter 2 family calculus.

`UnitCounitData` contains the normalized expressions available before proving
triangle identities; `Adjunctions` uses those same definitions. For component
triangles, read `RawComponentTriangles` for the shared frame comparisons and
`ComponentTriangles` for the three-step deduction from an adjunction's triangle
identities. For composition of adjunctions, `CompositeFormulas` supplies the
formulas and their comparisons before `CompositeTriangleAlgebra` proves their
triangles. General associativity and postcomposition calculations belong to
Chapter 2's `ExpressionCalculus`, whose derived laws also apply to any other
instance of that interface.
Formula-only clients use `ExpressionOperations`, the earlier package of chosen
opaque operations and construction comparisons. The full calculus adds laws
for those same operations; naming a composite therefore does not require
importing its associativity proof.
`HomAdjunctions` proves the forward implication of the hom-adjunction criterion;
its converse remains to be formalized.
`AdjunctionCalculus/HomUnitFormula` and `HomCounitFormula` compute these
functors through the unit and counit. Cancelling an invertible component
proves the corresponding hom-postcomposition equivalence for an adjoint
section. `EvaluationHomEquivalences` applies this to homs into and out of
identity arrows; it also identifies normalized source evaluation on homs
into an identity arrow with precomposition by the original arrow.

`UniquenessOfAdjoints` proves uniqueness of right adjoints by comparing
their universal counits and applying Rezk recognition. The shared
`ExpressionCalculus` packages the already proved operations and laws to
keep this calculation small for Agda.

`InitialAndTerminalObjects.IntervalDisjointness` proves the reverse hom
category of the interval equivalent to the empty category. The proof works
over that whole hom category and uses the interval core and disjointness.
`AdjunctionCalculus.NormalizedSections` constructs both kinds of adjoint
section from a specified section identification and the two normalized
transformation equations. The converse characterization remains separate.
`EvaluationAdjunctions` proves that target evaluation is left adjoint to
the constant-arrow functor, which is left adjoint to source evaluation.
It includes the corresponding adjoint-section and Bousfield-localization
structures. `EvaluationDeformations` supplies the max/min transformations;
their normalization retains both endpoint frames. Rezk is used to recover
the identification on the constant-arrow section. The proof does not use
functoriality of universals.

`EquivalenceAdjunctions` constructs an adjunction from an equivalence and
a specified inverse, retaining invertibility of both unit and counit.
Consequently every equivalence has both kinds of adjoint section and
Bousfield localization. This construction uses no square or Rezk axiom.

`CompositeAdjunctions` constructs composite adjunctions with both triangles
and proves closure of adjoint sections and both Bousfield localizations.
`SectionNormalizationConverse` recovers both normalization equations from
an arbitrary adjoint section, using its Rezk section identification.
`RelativeAdjunctions` supplies the normalized over-base records.
`RelativeUnitCriterion` proves both implications between the unit and counit
conditions for a fixed underlying adjunction. `NamedMorphisms` and
`DecodedMorphisms` construct actual arrows in the relative functor category
from transformations over the base and conversely; inverse laws and
compatibility with composition remain separate obligations.
Supporting transformation operations are in
`Chapter03/RelativeCategories/Morphisms`, `MorphismWhiskering`, and
`MorphismRetargeting`.

`RelativeComposition` proves composition of normalized relative adjunctions;
`RelativeSectionComposition` proves composition of both types of relative
adjoint section. Relative base change remains open.

`FunctorCategoryComponents` constructs the units and counits for
postcomposition and contravariant precomposition. `PostcompositionAdjunctions`
and `PrecompositionAdjunctions` now supply the actual adjunctions with both
triangle identities. The precomposition proof retains the chosen common middle
frame, normalizes both parameter-change endpoints, and reflects the evaluated
component triangles. The supporting Chapter 2 calculus proves recovery after
uncurrying (`CurryingUncurryingRecovery`) and reflection of full framed
identifications (`UncurryingReflection`). These retain both endpoint
equations and do not use functoriality of universals.
`UncurryingCurryingRecovery` proves the opposite inverse comparison.
`FunctorCategoryEvaluation` applies it to all four chosen unit and counit
diagrams. Uncurrying also commutes with endpoint changes and parameter
restriction, with the specified comparison identifications.

`FunctorCategoryLocalizations` proves postcomposition preserves both adjoint
sections and both Bousfield localizations. `UncurryingInvertibility` transports
and reflects full inverse witnesses; no pointwise detection is used.
`RelaxedAdjointSections` proves both relaxation criteria by correcting an
invertible restriction of the relative deformation to the chosen section.
`AdjointSectionBaseChange` then constructs both kinds of adjoint section on
any specified absolute pullback cone. `LocalizationFibers` gives initial or
terminal objects in its absolute fibers, with their section-image comparisons.
`SliceUniversalObjects` gives terminal objects of slices and initial objects
of coslices, retaining their identity-arrow image comparisons.
These results do not use functoriality of universals.

`DirectedEvaluationBaseChange` proves the source and target directed-evaluation
squares are pullbacks, using one-sided universal maps. The identification of
those maps with the earlier two-sided directed-pullback action is separate.

In Section 4.5, `Fibrations` defines the two fibration structures,
and `LeftAndRightFibrations` proves that left/right fibrations are
cocartesian/cartesian, including both assertions for equivalences.
`Transport` constructs parameterized lifts with their complete endpoint
cone comparisons, and `FiberTransport` gives actual functors between
fibers. `TransportRestriction` compares lifts of literally restricted cones.
`UniversalLifts` constructs adjoint sections of the parameterized lift
projections and universal objects of their absolute fibers.
`LiftHomEquivalences` identifies homs from the endpoint of a chosen covariant
lift with homs between its literal directed image and that of an identity
arrow. The source of the filling computes to precomposition. It also
constructs the dual hom equivalence for cartesian lifts. The stronger
hom-pullback property of globally cocartesian arrows and the transport
identity/composition laws remain separate obligations. `BaseChange` proves
closure under arbitrary specified absolute pullback squares, and
`EquivalenceInvariance` transports either fibration structure along a square
whose horizontal arrows are equivalences. `Projections` gives both fibration
structures for terminal maps and both product projections. Its `OverGroupoid`
construction gives both structures to every absolute functor with groupoid
base. `Composition` proves
closure under composition and retains the comparison with the explicit composite
of the two sections. Its supporting `CompositeBaseChange` performs the generic
adjoint-section calculation before specializing the pullback square.
`CocartesianMorphisms` retains the specified hom-square matching in the
cartesian and cocartesian definitions. `CocartesianIsomorphisms` proves
that isomorphisms satisfy both conditions and that either condition detects
isomorphisms when the image is invertible. These results concern absolute
endpoints; contextual inheritance is a separate obligation.

Coverage is partial. The existing material constructs directed pullbacks,
left/right fibrations and transport, ordinary slices, and framed adjunction
data. `GeneralSliceFibrations` also proves the absolute general-slice and
coslice projection theorems for the existing Chapter 3 cylinder definitions.
It does not yet prove all transport laws or the general adjunction
characterization. Sections 4.5–4.8 concern (co)cartesian fibrations,
source/target fibrations, cocartesian functors, and local fibrations; their
formalization is being continued. Sections 4.6–4.8 are not yet implemented.
An aggregate is not a completeness claim.

The former Chapter05 namespace is now Chapter04. Previously formalized limits
and colimits are retained separately under `VolumeI/Deferred/LimitsAndColimits/`,
matching the manuscript's deferred `tmp.tex` material. They remain registered
for checking but are not part of Chapter 4's coverage.


The generic cospan-fiber constructions are in Chapter 1, Section 6:
`Cospans/FiberImages` maps fiber cones with their full matchings;
`Cospans/Fibers` constructs the comparison and reconstruction between the
total fiber and the pullback of component fibers. It retains complete
factorization computations and a higher comparison recovering the
transported compatibility witness. `ConeCalculus/SquareTransport` supplies
the equivalence of witness animae used in this recovery.

`FiberInterchangeProjections`, `FiberInterchangeSquare`, and
`FiberInterchange` give a separate pasting proof: the pullback of component
fibers is equivalent to the fiber of the induced pullback functor. The
specified pasted fiber cone and its whole factorization computation are
retained. This theorem does not identify the earlier `Fibers` comparison
and reconstruction as inverses. The specialization to homs and comparison
with the specified cocartesian hom-pullback matching remain to be proved.


The coslice route separates the chosen-lift argument from the hom-fiber
calculation. In Section 4.4, `CosliceAdjunctions` and
`AdjointSectionCosliceSquares` give the coslice pullback of a left adjoint
section, retaining the recovered unit identification. Section 4.5's
`SourceRestrictedLifts` applies this to the lifting adjunction.
`IteratedCoslicePrecomposition` identifies the projections of the iterated
coslices with precomposition. These results retain the transported
vertical maps; their comparison with the induced base functor is separate.

For the fiber calculation, Section 4.3's `MappingCalculus/CosliceHomFibers`
uses the universal hom expression for the fiber inclusion.
`CoslicePrecompositionFamilies` and `CosliceFiberPrecomposition` show that
coslice precomposition restricts to the specified hom-precomposition
functor, and prove that its square with the fiber inclusions is a pullback.
`CosliceImageFamilies` and `CosliceFiberImages` compare functorial images on
coslices with the literal hom-postcomposition functor, retaining the full
endpoint comparisons and their projection equations. The supporting
`ConstantSourceImages` calculus belongs to Chapter 2, and `Pasting/FiberSquares`
belongs to Chapter 1.

`CosliceCompositionNaturality` constructs the coslice composition square
through a common normalized expression. `CosliceTriangleHomFibers`
identifies triangles with prescribed final target with the corresponding
hom category, retaining literal hom-precomposition. `LiftTriangleSquares`
applies the chosen-lift coslice pullback to these triangle presentations.
Its other map is `triangle-image`, constructed by the universal property;
it has not yet been identified with hom-postcomposition.

`CosliceHomCriterion` separates the pasting-and-cancellation argument from
its outstanding computation: it deduces the existing specified hom
pullback from the coslice pullback **and** an explicit equality of the
two outer-rectangle matchings. This is a conditional criterion, not a
completed proof that the chosen lift is cocartesian.

These checked fiber maps do not yet establish the cocartesian hom-pullback
criterion. Agreement with its prescribed commutativity witness, and the
comparison of the flattened chosen-lift square with the image square,
remain explicit obligations. No generic coherence of independently
specified interchange witnesses is assumed.

## Chapter 5

Chapter 5 develops the separately axiomatized contextual theory. A contextual
theorem must not be read as a theorem under Chapter 3 assumptions.
Its [own guide](src/SCT/VolumeI/Chapter05/Guide.md) records the assumptions and
coverage in more detail.

1. Start Section 6.1 with `Contexts`, `Core`, `Coherence`,
   `PrimitivePreservation`, and `Changes`. `Expressions/` gives recursive
   comparisons of functors, identifications, and witnesses;
   `ComparisonCalculus/` supplies the supporting boundary calculations.
2. Section 6.2 retains `DependentProducts`, `DependentSums`,
   `ProductFunctoriality`, `SumFunctoriality`, `ProductMapping`, `SumMapping`,
   `Frobenius`, and `ProductPullbacks`. Supporting proofs are grouped in
   `ProductCalculus/` and `MappingCalculus/`.
3. In Section 6.3 read `GenericPoint`, `GenericFiber`, `Recovery`,
   `PairPullbacks`, `RecoverEquivalence`, `SumPullbacks`, `ConstantFamilies`,
   and `LocalMappingOverBase`. `SumPullbacks` proves that the total cone
   constructed by extension is a pullback. `SumConeMatching` identifies its
   matching with the formula using the sum compositor and congruence;
   `direct-square-isPullback` gives the pullback property for that exact cone.
4. Section 6.4 contains substitution and its total-category pullback theorem,
   supported by `SubstitutionCalculus/`. Section 6.5 contains the first three
   exercises.
5. Coverage remains partial. The full constructor-witness comparison,
   the named relative-triangle comparison, forward preservation of animae,
   the iterated-context equivalence, and higher compatibility between
   change-of-context routes remain open. Consult the chapter guide for the
   current precise coverage boundary.

Mathematical source files use `.lagda.md`: prose explains the construction,
and fenced Agda blocks give its precise statement and proof. The specified
comparison identifications are part of the mathematics, including in helper
modules whose names and layout have changed.

## Pairing comparisons and product coherence

For the calculation infrastructure in Chapter 1, Section 3, read
`ProductCalculus/PairingInterface` and `ProductCalculus/ChosenPairing` first.
They separate the chosen comparisons from their projection triangles.
`IdentificationCalculus/FunctorCoherence` supplies the general pentagon,
triangle, and unitor calculations used by several constructions.

`ProductCalculus/IteratedPairing`, `PairingUnits`, and `ProductFunctorUnits`
contain the projection arguments. Each proves the calculation with pairing
operations and laws as parameters, then specializes it to the chosen
comparisons. Their final concrete declarations retain the book's notation.
The common pasting calculation is in `SCT.Calculus.Pasting`, realized for
absolute identifications by `IdentificationCalculus/VerticalComposition`.

`SCT.Calculus.Squares` contains pasting arguments for specified comparison
routes. Its applications pass the actual square and cancellation witnesses.
The two composition input modules in Section 1.4 retain the route calculations,
then use these generic pastings to compare them. `Substitution/ProofCalculus`
realizes the algebra with the same coherence comparisons used by those proofs.

`ProductCalculus/ProductPairing` studies a product functor applied to a pair,
with both projection witnesses. Its basic operation is in
`PairingInterface.Constructions`; the projection arguments take their three
higher comparisons explicitly. `ChosenComparisons` supplies those already
selected in the formalization. The older Section 1.4 entry point remains
available for existing readers and callers.


`Equivalences.TerminalTargets` proves that identifications with terminal
codomain agree, directly from equivalence reflection. This elementary fact
is available before the mapping-anima and identity-evaluation calculations.

For nested applications, `Squares.NestedRoute` assembles the final diagram
from its restriction, naturality, and input-combination squares. The concrete
module `Substitution/NestedApplicationRestriction` still proves those squares.
`CompositionCalculus/UniversalCoherenceCalculus` similarly keeps its retained
routes and reflection argument, using `Squares.normalization-naturality` and
`normalized-frame-square` for the intervening pastings. Elementary square
pasting comes directly from `IdentificationCalculus/CoordinateNaturality`;
it does not require the internal pentagon theorem.

For the retained triangle, `Substitution/CoherenceTransport.inverse-route-image`
cancels the two target comparisons of a route before changing endpoints.
`RetainedComparisonLaws.TriangleCalculation` supplies the actual retained
associator and its image computation. The higher comparison
`inverse-route-image-computation` records the precise cancellation route;
the main triangle argument remains in `TriangleCalculation`.

`CoherenceTransport.prewhiskered-composite` and `postwhiskered-composite`
normalize a whiskered composite comparison followed by an incoming comparison.
The pentagon in `CompositionCalculus/InternalPentagon` uses these laws for
its four vertex-comparison normalizations. Its edge squares and the final
comparison with the primitive pentagon remain in that module.


`SquareCalculus/ParameterSquareNaturality` supplies the one-variable forms
of naturality for pasted parameter squares. `paste-natural-outer` and
`paste-natural-inner` are used in both the associator and unit comparisons.
`paste-comparison-chain` assembles successive comparison squares with their
whiskered boundaries. Its `outer` and `inner` forms combine this assembly
with naturality in the changing side of a pasted square. The associator
proof uses these forms after normalizing its two composition squares.
Each has a higher computation statement recording its selected formula. `UniversalCoherence` and `UniversalUnitCalculus`
still construct and normalize the actual squares before applying these laws.


`UniversalUnitCalculus.paste-three-comparisons` performs the final assembly
of the composition, identity, and unit squares. Both unit proofs still
construct these three squares explicitly. Its computation statement refers
to the transparent construction `three-comparison-pasting`, which displays
the chosen formula once.


`UniversalCoherenceCalculus` also treats naturality of a unit route before
specializing it to retained evaluations. The left and right pastings combine
the given composition square with interchange and unitor naturality.
`RouteNaturality` supplies the actual retained comparison, so its argument
continues to display the mapping-anima construction.


`Substitution/ComparisonCancellation` also transports triangles and pentagons
along specified comparisons of their edges. `UniversalCoherence` supplies
its three or five actual edge comparisons to these laws. The supporting
`TriangleTransport` and `PentagonTransport` modules expose their chosen
pastings and higher computation statements, so the selected coherence
witnesses remain accessible.


`Section06/Cospans/PairedSquares` and `PairedMaps` pair specified cospan
squares with coordinate computation laws. `ProjectedImages` proves that
compatible projections commute with whole cone images; the restriction
calculation lives in `Coordinates/ProjectedSquareRestriction`.
`Chapter02/Section04/PullbackCalculus/PairedEvaluationCones` applies these
results to two evaluations. Its cube retains the mapped-cone and product
matchings and does not require a pullback hypothesis on the original cone.


`Cospans/PullbackCubeFibers` extends the specified fiber-interchange cone
to arbitrary presentations of a pullback cube, retaining its whole lifted
comparison and fiber computation. `PairedEvaluationFibers` in Chapter 2
applies it to paired evaluation over a pullback. Its component families
remain canonically represented; identification of their maps with the
selected hom-post operations is a separate step.


`Chapter02/Section06/HomCalculus/PullbackFamilies` specializes the endpoint
fiber theorem to literal hom categories. It identifies all three represented
component fibers with their expected hom categories and retains the whole
family-change computations. Identification of the maps and the final
hom-square matching remains separate.

`Coordinates/BoundaryTransport` supplies the general boundary calculation
used by `PairedEvaluationImages`. The latter computes both endpoint
coordinates of an image cone with an arbitrary target-family comparison.
`HomCalculus/FramedFiberImages` compares that entire image cone with the cone
of a postcomposed and retargeted morphism expression. It retains the actual
paired-square matching and displays both endpoint changes. The right map
in the eventual hom pullback includes endpoint transport along the original
cone matching, in addition to postcomposition.


`Coordinates/ProductFamilyFrames` computes the selected product-family
comparison at each endpoint, including parameter restriction.
`Coordinates/ProductConeFrames` then identifies restricted product cones
with literal productMap-pair legs and computes their paired matchings.
`Cospans/FamilyChange` and `FiberImageFamilyChange` retain the whole cone
computations when changing a fiber family and when conjugating its image.

`HomCalculus/HomFiberPostcomposition` identifies the actual paired fiber-image
map with the selected hom-post functor. `HomFamilyPostcomposition` allows
specified endpoint-family identifications and target endpoint transport.
`PullbackHomMaps` applies these comparisons to the actual fiber diagram and
proves that its transported hom cone is a pullback.
`PullbackEndpointFrames` identifies the endpoint transport with the inverse
pair of the original square's endpoint matchings. The remaining obligations
are the literal vertex hom-post legs and their compatibility with the final
specified hom-square matching. These results do not yet prove the
cocartesian hom-pullback criterion.
