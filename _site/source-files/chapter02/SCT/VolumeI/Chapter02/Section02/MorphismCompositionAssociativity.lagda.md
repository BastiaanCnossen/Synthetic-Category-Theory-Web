# Associativity with specified endpoints

For three composable morphism families, glue the first composite triangle
to its source-unit triangle, and the second composite triangle to its
target-unit triangle. The two squares share the original middle arrow.
Their horizontal composition has the two bracketings as horizontal edges
and the original identity families as vertical edges.

This is the square construction in `prop:Composition_Is_Associative`.
All data are families in an arbitrary categorical parameter `P`; the
framed-square interface retains every prescribed endpoint comparison.
The endpoint-preserving commutativity comparison for that square, followed
by the two unit comparisons, identifies the bottom edge with the top edge.
Taking `P` to be the category of composable triples gives naturality.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.MorphismCompositionAssociativity where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitˡ-One)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair⁼-id-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction using (pair-evaluation-natural-One)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
  using (category-over; FunctorOverBase; functor-over)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
  using (CompatibleOver; IdentificationOver; compatible-to-over)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
  using (Pullback; pullback-cone; pullback₁; pullback₂; pullback-match)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification; identity-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons
  using (compose-family-comparisons; inverse-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFraming using (endpoint-triangle)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (Composable)
open import SCT.VolumeI.Chapter02.Section02.SegalAxiom using (segal-isEquiv)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC
open MC using (module ComposableFamilies)
open import SCT.VolumeI.Chapter02.Section02.SegalComposition using (module ChosenComposition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionComparisons
  using (module CompositionComparisons)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionUnits
  using (module FamilyUnitPresentations; module MorphismCompositionUnits)
open import SCT.VolumeI.Chapter02.Section02.GluedFramedSquares
  using (module Glue)
open import SCT.VolumeI.Chapter02.Section02.FramedSquares
  using (FramedSquare; module SquareComposition)
import SCT.VolumeI.Chapter02.Section02.FramedSquareCommutativity as SquareCommutativity

private
  module _ {Γ : Context} {P C : CAT Γ} {x w : MAP P C} where
    family-comparison-over-endpoints : (alpha beta : MorphismFamily x w)
      → MorphismFamilyIdentification One alpha beta
      → IdentificationOver {A = One}
          {X = category-over P (pair x w)}
          {Y = category-over (Ar C) (pair ev₀ ev₁)}
          (functor-over (MorphismFamily.arrow alpha) (endpoint-triangle alpha))
          (functor-over (MorphismFamily.arrow beta) (endpoint-triangle beta))
    family-comparison-over-endpoints alpha beta given = record
      { identification = Compared.identification
      ; over = compatible-to-over paired-compatible }
      where
        module A = MorphismFamily alpha
        module B = MorphismFamily beta
        module Compared = FamilyComparison given using (identification; source; target)
        paired-compatible : CompatibleOver (pair ev₀ ev₁)
          (endpoint-triangle alpha) (endpoint-triangle beta) Compared.identification
        paired-compatible = comp₌-unitˡ-One (endpoint-triangle alpha) ∙
          (comp₌-cong (pair⁼-id-One x w) (id₌ (endpoint-triangle alpha)) ∙
            pair-evaluation-natural-One ev₀ ev₁ Compared.identification
              A.source-frame B.source-frame A.target-frame B.target-frame
              (id₌ x) (id₌ w)
              ((comp₌-unitˡ-One A.source-frame) ⁻¹ ∙ Compared.source)
              ((comp₌-unitˡ-One A.target-frame) ⁻¹ ∙ Compared.target))

module AssociativitySquare {Γ : Context} {P C : CAT Γ}
  {x y z w : MAP P C}
  (alpha : MorphismFamily x y) (beta : MorphismFamily y z)
  (gamma : MorphismFamily z w) where
  private
    module Chosen = MC.Composition C (segal-isEquiv C) using (compose)
    module Presentations = CompositionComparisons C (segal-isEquiv C)
      using (composition-presentation)

  first-composite : MorphismFamily x z
  first-composite = Chosen.compose beta alpha

  second-composite : MorphismFamily y w
  second-composite = Chosen.compose gamma beta

  first-square : FramedSquare alpha beta (identity-family x) first-composite
  first-square = Glue.value
    (Presentations.composition-presentation beta alpha)
    (FamilyUnitPresentations.source first-composite)

  second-square : FramedSquare second-composite (identity-family w) beta gamma
  second-square = Glue.value
    (FamilyUnitPresentations.target second-composite)
    (Presentations.composition-presentation gamma beta)

  top : MorphismFamily x w
  top = Chosen.compose second-composite alpha

  bottom : MorphismFamily x w
  bottom = Chosen.compose gamma first-composite

  value : FramedSquare top (identity-family w) (identity-family x) bottom
  value = SquareComposition.Compose.value C (segal-isEquiv C)
    (segal-isEquiv (Ar C)) first-square second-square

module _ {Γ : Context} {P C : CAT Γ} {x y z w : MAP P C} where
  associativity : (alpha : MorphismFamily x y) (beta : MorphismFamily y z)
    (gamma : MorphismFamily z w)
    → MorphismFamilyIdentification One
        (MC.Composition.compose C (segal-isEquiv C) gamma
          (MC.Composition.compose C (segal-isEquiv C) beta alpha))
        (MC.Composition.compose C (segal-isEquiv C)
          (MC.Composition.compose C (segal-isEquiv C) gamma beta) alpha)
  associativity alpha beta gamma = compose-family-comparisons
    (MorphismCompositionUnits.target-unit C (segal-isEquiv C) Square.top)
    (compose-family-comparisons
      (SquareCommutativity.comparison C (segal-isEquiv C) Square.value)
      (inverse-family-comparison
        (MorphismCompositionUnits.source-unit C (segal-isEquiv C) Square.bottom)))
    where
      module Square = AssociativitySquare alpha beta gamma using (top; bottom; value)
```

## The universal composable triple

The iterated pullback below retains its actual two matching identifications.
The second and third universal arrows use their inverses as source frames.
The input cones for chosen composition are then formed from these framed
families, and their complete factorization comparisons are retained. They
are not silently identified with another choice of triple projections.

```agda
module UniversalTriple {Γ : Context} (C : CAT Γ) where
  private
    pair-target : MAP (Composable C) C
    pair-target = ev₁ ∘ pullback₂ {f = ev₁ {C = C}} {g = ev₀}

  Triples : CAT Γ
  Triples = Pullback pair-target (ev₀ {C = C})

  pairs : MAP Triples (Composable C)
  pairs = pullback₁ {f = pair-target} {g = ev₀ {C = C}}

  third-arrow : MAP Triples (Ar C)
  third-arrow = pullback₂ {f = pair-target} {g = ev₀ {C = C}}

  first-pair : Cone (ev₁ {C = C}) ev₀ Triples
  first-pair = cone-restrict pairs (pullback-cone (ev₁ {C = C}) ev₀)

  first-arrow : MAP Triples (Ar C)
  first-arrow = Cone.left first-pair

  second-arrow : MAP Triples (Ar C)
  second-arrow = Cone.right first-pair

  first-matching : (ev₁ ∘ first-arrow) =₁ (ev₀ ∘ second-arrow)
  first-matching = Cone.match first-pair

  second-matching : (pair-target ∘ pairs) =₁ (ev₀ ∘ third-arrow)
  second-matching = pullback-match {f = pair-target} {g = ev₀ {C = C}}

  x y z w : MAP Triples C
  x = ev₀ ∘ first-arrow
  y = ev₁ ∘ first-arrow
  z = ev₁ ∘ second-arrow
  w = ev₁ ∘ third-arrow

  first : MorphismFamily x y
  first = record { arrow = first-arrow; source-frame = id₌ x; target-frame = id₌ y }

  second : MorphismFamily y z
  second = record
    { arrow = second-arrow; source-frame = first-matching ⁻¹; target-frame = id₌ z }

  third : MorphismFamily z w
  third = record
    { arrow = third-arrow
    ; source-frame = comp-assoc pairs (pullback₂ {f = ev₁ {C = C}} {g = ev₀}) ev₁ ∙
        (second-matching ⁻¹)
    ; target-frame = id₌ w }

  private
    module Chosen = MC.Composition C (segal-isEquiv C) using (compose)

  first-composite : MorphismFamily x z
  first-composite = Chosen.compose second first

  second-composite : MorphismFamily y w
  second-composite = Chosen.compose third second

  module FirstInput = ComposableFamilies first second using (cone; pair-map; pair-image)
  module SecondInput = ComposableFamilies second third using (cone; pair-map; pair-image)
  module LeftInput = ComposableFamilies first second-composite using (cone; pair-map; pair-image)
  module RightInput = ComposableFamilies first-composite third using (cone; pair-map; pair-image)

  left-bracketing right-bracketing : MorphismFamily x w
  left-bracketing = Chosen.compose third first-composite
  right-bracketing = Chosen.compose second-composite first

  comparison : MorphismFamilyIdentification One left-bracketing right-bracketing
  comparison = associativity first second third

  left-functor right-functor : MAP Triples (Ar C)
  left-functor = ChosenComposition.composition C (segal-isEquiv C) ∘ RightInput.pair-map
  right-functor = ChosenComposition.composition C (segal-isEquiv C) ∘ LeftInput.pair-map

  left-over : FunctorOverBase (category-over Triples (pair x w))
    (category-over (Ar C) (pair ev₀ ev₁))
  left-over = functor-over left-functor (endpoint-triangle left-bracketing)

  right-over : FunctorOverBase (category-over Triples (pair x w))
    (category-over (Ar C) (pair ev₀ ev₁))
  right-over = functor-over right-functor (endpoint-triangle right-bracketing)

  naturality : IdentificationOver {A = One} left-over right-over
  naturality = family-comparison-over-endpoints left-bracketing right-bracketing comparison
```
