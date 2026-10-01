# Slice evaluation squares from the Segal axiom

Paste the endpoint edge square with the Segal square and compare the
complete rectangle with evaluation of the slice projection. The endpoint
comparison supplies exactly the common edge frame needed by pasting.

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
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceArrowTriangles as Presentations


import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEndpointCones as EndpointCones
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEdgePullbacks as EdgePullbacks
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceSegalCones as SegalCones
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.CompositeEvaluationCones as Composite
import SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonPasting as Pasting

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEvaluationPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.Composition 𝒯 M ℱ P I E S
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I using (module Criterion)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯 using (compositeCone)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneIso-swap; coneSwap-pre; coneSwap-swap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse; inverse-identity)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)

module Slice {C : CAT} (x : Obj-abs C) where
  module End = EndpointCones.Slice 𝒯 M ℱ P I E S Q x
    using (comparison; comparison-left; module Source; module Boundary)
  module Arrows = Presentations.SliceAt 𝒯 M ℱ P I E S Q x
    using (forward; isEquiv; normalized-comparison)
  module Edge = EdgePullbacks.Slice 𝒯 M ℱ P I E S Q x using (square; square-isPullback)
  module Corner = SegalCones.Slice 𝒯 M ℱ P I E S Q x using (comparison; square; segal)
  open End.Boundary using (t; image)
  a₀ = Cone.left End.Source.square
  F = Arrows.forward
  e = ev₁ ∘ F
  α = ConeIso.leftIso End.comparison
  β = ConeIso.leftIso Arrows.normalized-comparison
  ε = End.Boundary.LeftParameter.boundary′
  K = Criterion.target-square (ev₀ ∘ a₀)
  module Eval = Composite.At.Restrict 𝒯 M ℱ one a₀ ev₀ F using (framed-comparison)
  segal = coneSwap Corner.segal

  inner : Cone a₀ edge₀ End.Boundary.Presentation.category
  inner = record { left = e ; right = t ; match = α }

  abstract
    inner-isPullback : IsPullback inner
    inner-isPullback = pullback-cone-invariant
      (cone-match-change _ _ _ _ (inverse-inverse α))
      (pullback-swap Edge.square Edge.square-isPullback)

  swapped-corner-raw : ConeIso (coneSwap (conePre (Cone.left image) Corner.square)) (conePre t segal)
  swapped-corner-raw = coneIso-compose (coneIso-inverse (coneSwap-pre t Corner.segal))
    (coneIso-swap Corner.comparison)
  swapped-corner : ConeIso (coneSwap (conePre (Cone.left image) Corner.square)) (conePre t segal)
  swapped-corner = coneIso-adjust swapped-corner-raw ε (ConeIso.rightIso swapped-corner-raw)
    (isoComp-unitˡ-at ε ∙ isoComp-cong (inverse-identity _) (idIso ε)) (idIso _)

  outer-comparison : ConeIso (compositeCone a₀ ev₀ (coneSwap (conePre F K))) (conePre t segal)
  outer-comparison = coneIso-compose swapped-corner
    (coneIso-compose (coneIso-swap (cone-action Corner.square β)) Eval.framed-comparison)

  abstract
    outer-frame : ConeIso.leftIso outer-comparison =₂ (α ∙ (a₀ ◁ idIso e))
    outer-frame = isoComp-cong (idIso α) ((postWhisker-idIso a₀ e) ⁻¹) ∙
      ((isoComp-unitʳ-at α) ⁻¹ ∙ (End.comparison-left ⁻¹))

  module Paste = Pasting.At 𝒯 P a₀ ev₀ ev₁ segal
    (pullback-swap (triangle-cone C) (Segal.SegalAxiom.segal-isPullback S C))
    inner inner-isPullback (coneSwap (conePre F K)) (idIso e) outer-comparison outer-frame
    using (square-isPullback)

  abstract
    restricted-isPullback : IsPullback (conePre F K)
    restricted-isPullback = pullback-cone-invariant (coneSwap-swap (conePre F K))
      (pullback-swap (coneSwap (conePre F K)) Paste.square-isPullback)

    evaluation-isPullback : IsPullback K
    evaluation-isPullback = equiv-cancel-right F (pullbackLift K) Arrows.isEquiv
      (equiv-transport (pullbackLift-restrict F K) restricted-isPullback)

module Coslice {C : CAT} (x : Obj-abs C) where
  module End = EndpointCones.Coslice 𝒯 M ℱ P I E S Q x
    using (comparison; comparison-left; module Source; module Boundary)
  module Arrows = Presentations.CosliceAt 𝒯 M ℱ P I E S Q x
    using (forward; isEquiv; normalized-comparison)
  module Edge = EdgePullbacks.Coslice 𝒯 M ℱ P I E S Q x using (square; square-isPullback)
  module Corner = SegalCones.Coslice 𝒯 M ℱ P I E S Q x using (comparison; square; segal)
  open End.Boundary using (t; image)
  a₀ = Cone.left End.Source.square
  F = Arrows.forward
  e = ev₀ ∘ F
  α = ConeIso.leftIso End.comparison
  β = ConeIso.leftIso Arrows.normalized-comparison
  ε = End.Boundary.LeftParameter.boundary′
  K = Criterion.source-square (ev₁ ∘ a₀)
  module Eval = Composite.At.Restrict 𝒯 M ℱ zero a₀ ev₁ F using (framed-comparison)
  segal = coneSwap Corner.segal

  inner : Cone a₀ edge₂ End.Boundary.Presentation.category
  inner = record { left = e ; right = t ; match = α }

  abstract
    inner-isPullback : IsPullback inner
    inner-isPullback = pullback-cone-invariant
      (cone-match-change _ _ _ _ (inverse-inverse α))
      (pullback-swap Edge.square Edge.square-isPullback)

  swapped-corner-raw : ConeIso (coneSwap (conePre (Cone.left image) Corner.square)) (conePre t segal)
  swapped-corner-raw = coneIso-compose (coneIso-inverse (coneSwap-pre t Corner.segal))
    (coneIso-swap Corner.comparison)
  swapped-corner : ConeIso (coneSwap (conePre (Cone.left image) Corner.square)) (conePre t segal)
  swapped-corner = coneIso-adjust swapped-corner-raw ε (ConeIso.rightIso swapped-corner-raw)
    (isoComp-unitˡ-at ε ∙ isoComp-cong (inverse-identity _) (idIso ε)) (idIso _)

  outer-comparison : ConeIso (compositeCone a₀ ev₁ (coneSwap (conePre F K))) (conePre t segal)
  outer-comparison = coneIso-compose swapped-corner
    (coneIso-compose (coneIso-swap (cone-action Corner.square β)) Eval.framed-comparison)

  abstract
    outer-frame : ConeIso.leftIso outer-comparison =₂ (α ∙ (a₀ ◁ idIso e))
    outer-frame = isoComp-cong (idIso α) ((postWhisker-idIso a₀ e) ⁻¹) ∙
      ((isoComp-unitʳ-at α) ⁻¹ ∙ (End.comparison-left ⁻¹))

  module Paste = Pasting.At 𝒯 P a₀ ev₁ ev₀ segal
    (pullback-swap (coneSwap (triangle-cone C))
      (pullback-swap (triangle-cone C) (Segal.SegalAxiom.segal-isPullback S C)))
    inner inner-isPullback (coneSwap (conePre F K)) (idIso e) outer-comparison outer-frame
    using (square-isPullback)

  abstract
    restricted-isPullback : IsPullback (conePre F K)
    restricted-isPullback = pullback-cone-invariant (coneSwap-swap (conePre F K))
      (pullback-swap (coneSwap (conePre F K)) Paste.square-isPullback)

    evaluation-isPullback : IsPullback K
    evaluation-isPullback = equiv-cancel-right F (pullbackLift K) Arrows.isEquiv
      (equiv-transport (pullbackLift-restrict F K) restricted-isPullback)

```
