# Composable morphisms as an anima

The Segal axiom also identifies `Map [2] C` with the anima of pairs of
composable morphisms. This is the equivalence used in the definition of
a collection closed under composition.

To retain its specified middle-vertex identification, first regard the
walking triangle as the pushout of its two short edges. The existing
functor-category criterion for pushouts then gives exactly the mapping
square we need. Terminal-domain evaluation compares the criterion with
the original Segal square.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingSegal
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open Segal 𝒯 M ℱ P I E
open Segal.SegalAxiom S
open Mapping.MappingAnimae M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M using (mapPre; mapPre-comp; mapPre-cong)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P
  using (FunctorCriterion; functorOut)
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorCriterionDetection 𝒯 M ℱ P
  using (functor-criterion→pushout)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointCornerComparison 𝒯 M ℱ P
  using () renaming (module At to Corner)
open import SCT.VolumeI.Chapter03.Section01.Lifting.EndpointPullbacks 𝒯 M ℱ P
  using () renaming (module At to EndpointPullbacks)

triangleSquare : Square one zero d₂ d₀
triangleSquare = record { commute = face-middle ⁻¹ }

abstract
  triangle-functor-criterion : FunctorCriterion triangleSquare
  triangle-functor-criterion C = EndpointPullbacks.conversion-reflects-pullback C
    (functorOut triangleSquare C)
    (pullback-cone-invariant (coneIso-inverse (Corner.comparison triangleSquare C))
      (segal-isPullback C))

  triangle-isPushout : IsPushout triangleSquare
  triangle-isPushout = functor-criterion→pushout triangleSquare triangle-functor-criterion

mappingTriangleCone : (C : CAT) →
  Cone (mapPre {D = C} one) (mapPre zero) (Map [2] C)
mappingTriangleCone = mappingOut triangleSquare

mappingTriangle-isPullback : (C : CAT) → IsPullback (mappingTriangleCone C)
mappingTriangle-isPullback = triangle-isPushout

ComposableMorphisms : CAT → CAT
ComposableMorphisms C = Pullback (mapPre {D = C} one) (mapPre zero)

mappingSegal : (C : CAT) → MAP (Map [2] C) (ComposableMorphisms C)
mappingSegal C = pullbackLift (mappingTriangleCone C)

abstract
  mappingSegal-isEquiv : (C : CAT) → IsEquiv (mappingSegal C)
  mappingSegal-isEquiv = mappingTriangle-isPullback

composeMorphisms : (C : CAT) → MAP (ComposableMorphisms C) (Map [1] C)
composeMorphisms C = mapPre d₁ ∘ IsEquiv.inverse (mappingSegal-isEquiv C)

module Completion (C : CAT) where
  q = mappingSegal C
  j = IsEquiv.inverse (mappingSegal-isEquiv C)

  completion-β : (q ∘ j) =₁ id (ComposableMorphisms C)
  completion-β = (IsEquiv.retractionIso (mappingSegal-isEquiv C)) ⁻¹

  short-edge : (r : MAP (ComposableMorphisms C) (Map [1] C))
    (e : MAP (Map [2] C) (Map [1] C)) → (r ∘ q) =₁ e → (e ∘ j) =₁ r
  short-edge r e β = comp-unitʳ r ∙
    ((r ◁ completion-β) ∙ (comp-assoc j q r ∙ (β ⁻¹ ▷ j)))

  first-edge : (mapPre d₂ ∘ j) =₁ (pullback₁ {f = mapPre {D = C} one} {mapPre zero})
  first-edge = short-edge pullback₁ (mapPre d₂) (pullbackLift-β₁ (mappingTriangleCone C))

  second-edge : (mapPre d₀ ∘ j) =₁ (pullback₂ {f = mapPre {D = C} one} {mapPre zero})
  second-edge = short-edge pullback₂ (mapPre d₀) (pullbackLift-β₂ (mappingTriangleCone C))

  source-vertex : (mapPre zero ∘ mapPre {D = C} d₁) =₁ (mapPre zero ∘ mapPre d₂)
  source-vertex = (mapPre-comp zero d₂) ⁻¹ ∙
    (mapPre-cong face-bottom ∙ mapPre-comp zero d₁)

  target-vertex : (mapPre one ∘ mapPre {D = C} d₁) =₁ (mapPre one ∘ mapPre d₀)
  target-vertex = (mapPre-comp one d₀) ⁻¹ ∙
    (mapPre-cong (face-top ⁻¹) ∙ mapPre-comp one d₁)

  compose-source : (mapPre zero ∘ composeMorphisms C) =₁
    (mapPre zero ∘ pullback₁ {f = mapPre {D = C} one} {mapPre zero})
  compose-source = (mapPre zero ◁ first-edge) ∙
    (comp-assoc j (mapPre d₂) (mapPre zero) ∙
      ((source-vertex ▷ j) ∙ (comp-assoc j (mapPre d₁) (mapPre zero)) ⁻¹))

  compose-target : (mapPre one ∘ composeMorphisms C) =₁
    (mapPre one ∘ pullback₂ {f = mapPre {D = C} one} {mapPre zero})
  compose-target = (mapPre one ◁ second-edge) ∙
    (comp-assoc j (mapPre d₀) (mapPre one) ∙
      ((target-vertex ▷ j) ∙ (comp-assoc j (mapPre d₁) (mapPre one)) ⁻¹))
```
