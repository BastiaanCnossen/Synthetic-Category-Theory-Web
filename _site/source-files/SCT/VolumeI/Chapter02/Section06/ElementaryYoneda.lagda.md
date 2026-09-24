# The elementary Yoneda criterion for isomorphisms

This proves `exercise:elementary_Yoneda_iso` for absolute morphisms.
An isomorphism induces equivalences by composition on either side.
Conversely, either family of equivalences detects an isomorphism; in fact,
only the tests at the source and target are needed for this direction.

The composition functors below act on the hom categories already defined
in Section 2.1. Their computation and cancellation laws retain the endpoint
identifications. The proof does not require the Rezk or recognition axioms.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter02.Section06.ElementaryYoneda
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section01.AbsoluteMorphisms 𝒯 M ℱ P I
  using (morphism-expression; morphism-in-hom)
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E using (IsInvertible; IsoLift)
open import SCT.VolumeI.Chapter02.Section03.InverseTriangleLift 𝒯 M ℱ P I E using (invertible-lift)
open import SCT.VolumeI.Chapter02.Section03.LiftedInverseWitnesses 𝒯 M ℱ P I E using (lift-invertible)
import SCT.VolumeI.Chapter02.Section06.HomCompositionEquivalences 𝒯 M ℱ P I E S Q as Action
import SCT.VolumeI.Chapter02.Section06.HomCompositionDetection 𝒯 M ℱ P I E S Q as Detection

module Criterion {C : CAT} {x y : Obj-abs C} (f : Morphism x y) where
  point = morphism-in-hom f
  open At point public using (postcompose; precompose)

  PostcompositionEquivalences PrecompositionEquivalences : Set m
  PostcompositionEquivalences = (z : Obj-abs C) → IsEquiv (postcompose z)
  PrecompositionEquivalences = (z : Obj-abs C) → IsEquiv (precompose z)

  private
    point-comparison = ExpressionIso.comparison (hom-β (morphism-expression f))

    point-lift : IsInvertible f → IsoLift (MorphismExpression.arrow (hom-expression point))
    point-lift w = record { lift = IsoLift.lift original
      ; comparison = point-comparison ⁻¹ ∙ IsoLift.comparison original }
      where original = invertible-lift f w

    read-lift : IsoLift (MorphismExpression.arrow (hom-expression point)) → IsInvertible f
    read-lift w = lift-invertible f (record { lift = IsoLift.lift w
      ; comparison = point-comparison ∙ IsoLift.comparison w })

  isomorphism-postcompose : IsInvertible f → PostcompositionEquivalences
  isomorphism-postcompose w = Action.InvertiblePoint.postcompose-isEquiv point (point-lift w)

  isomorphism-precompose : IsInvertible f → PrecompositionEquivalences
  isomorphism-precompose w = Action.InvertiblePoint.precompose-isEquiv point (point-lift w)

  postcompose-detects-isomorphism : IsEquiv (postcompose x) → IsEquiv (postcompose y) → IsInvertible f
  postcompose-detects-isomorphism at-source at-target =
    read-lift (Detection.Detect.FromPost.lift point at-source at-target)

  precompose-detects-isomorphism : IsEquiv (precompose x) → IsEquiv (precompose y) → IsInvertible f
  precompose-detects-isomorphism at-source at-target =
    read-lift (Detection.Detect.FromPre.lift point at-source at-target)

  postcompose-isomorphism : PostcompositionEquivalences → IsInvertible f
  postcompose-isomorphism tests = postcompose-detects-isomorphism (tests x) (tests y)

  precompose-isomorphism : PrecompositionEquivalences → IsInvertible f
  precompose-isomorphism tests = precompose-detects-isomorphism (tests x) (tests y)
```
