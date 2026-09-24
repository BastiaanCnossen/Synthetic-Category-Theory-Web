# The projection comparison of the currying corner

The two axis comparisons induce a corner matching. Its parameter
projection is the specified parameter comparison, and its rectangle
projection is assembled from the inner and outer coordinate equations.
Product reflection identifies that matching with their paired comparison.

`RectangularCornerNormalization` identifies this paired comparison with
the specified shape-corner route. `SquareCornerEvaluation` transports
that equation through double evaluation; `GluedSquareCorners` then uses
the supplied triangle vertex equations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.SquareCurryingCorner
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public
import SCT.VolumeI.Chapter02.Section02.SquareInsertionCorner as Corner
import SCT.VolumeI.Chapter02.Section02.SquareDiagramCorners as Diagram
import SCT.VolumeI.Chapter02.Section02.SquareParameterCorner as Parameter
import SCT.VolumeI.Chapter02.Section02.PairedProjectionComposition as Paired
import SCT.VolumeI.Chapter01.Section04.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as Pairing
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-iso-extensionality)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)
module PS = Projections 𝒯

module At (Γ A B : CAT) (u : Obj-abs A) (v : Obj-abs B) where
  module Input = Corner.At 𝒯 M ℱ Γ A B u v
  module Coordinates = Input.Coordinates
  module H = Input.H
  module V = Input.V
  module Inner = Diagram.InnerCoordinate 𝒯 M ℱ Γ A B u v
  module Outer = Diagram.OuterCoordinate 𝒯 M ℱ Γ A B u v
  module Param = Parameter.At 𝒯 M ℱ Γ A B u v
  ia = Input.ia
  ib = Input.ib
  χ = Input.corner
  J = Coordinates.permute
  rectangle = Coordinates.rectangle
  betaJ = pair-β₂ Coordinates.parameter rectangle
  module Source = Paired.At 𝒯 M ℱ Coordinates.inner Coordinates.outer H.step ib
    (pair-β₂ (id (Γ × B)) (const u)) (H.first-step pr₂)
    (const-pre u ib) (pair-β₂ (id Γ) (const v))
  module Target = Paired.At 𝒯 M ℱ Coordinates.inner Coordinates.outer V.step ia
    V.inner-step V.outer-step (pair-β₂ (id Γ) (const u)) (const-pre v ia)

  abstract
    direct-square : PS.Square rectangle Source.direct Target.direct χ
    direct-square = Paired.paired-square 𝒯 M ℱ Coordinates.inner Coordinates.outer
      Inner.incoming Inner.outgoing Outer.source-frame Outer.target-frame χ Inner.inner-square Outer.outer-square

    rectangle-square : PS.Square rectangle Source.composite Target.composite χ
    rectangle-square = Source.comparison ∙ direct-square ∙
      isoComp-cong (Target.comparison ⁻¹) (idIso (rectangle ◁ χ))

  source = PS.compose-base pr₂ H.restriction H.target-second ib Source.second
  target = PS.compose-base pr₂ V.restriction V.target-second ia Target.second
  stage₁ = PS.compose-base pr₂ (J ∘ H.step) H.source-second ib Source.second
  stage₂ = PS.compose-base pr₂ J betaJ (H.step ∘ ib) Source.composite
  stage₃ = PS.compose-base pr₂ J betaJ (V.step ∘ ia) Target.composite
  stage₄ = PS.compose-base pr₂ (J ∘ V.step) V.source-second ia Target.second
  matching = Param.matching

  abstract
    matching-rectangle : PS.Square pr₂ source target matching
    matching-rectangle = PS.compose-square pr₂ source stage₄ target Param.fifth _
      (PS.pre-square pr₂ ia V.source-second V.target-second Target.second V.comparison V.projection₂)
      (PS.compose-square pr₂ source stage₃ stage₄ Param.fourth _
        (PS.inverse-square pr₂ stage₄ stage₃ (comp-assoc ia V.step J)
          (PS.associator-square pr₂ J V.step ia betaJ V.rectangle-step Target.second))
        (PS.compose-square pr₂ source stage₂ stage₃ Param.third _
          (PS.post-square pr₂ J betaJ Source.composite Target.composite χ rectangle-square)
          (PS.compose-square pr₂ source stage₁ stage₂ Param.second Param.first
            (PS.associator-square pr₂ J H.step ib betaJ H.rectangle-step Source.second)
            (PS.inverse-square pr₂ stage₁ source (H.comparison ▷ ib)
              (PS.pre-square pr₂ ib H.source-second H.target-second Source.second H.comparison H.projection₂)))))

  parameter-comparison = Param.target ⁻¹ ∙ Param.source
  rectangle-comparison = target ⁻¹ ∙ source
  projection-comparison : (H.restriction ∘ ib) =₁ (V.restriction ∘ ia)
  projection-comparison = pair-iso parameter-comparison rectangle-comparison

  abstract
    comparison : matching =₂ projection-comparison
    comparison = pair-iso-extensionality
      ((pair-iso-β₁ parameter-comparison rectangle-comparison) ⁻¹ ∙
        isoComp-cong (idIso (Param.target ⁻¹)) Param.matching-parameter ∙
        (cancel-left Param.target (pr₁ ◁ matching)) ⁻¹)
      ((pair-iso-β₂ parameter-comparison rectangle-comparison) ⁻¹ ∙
        isoComp-cong (idIso (target ⁻¹)) matching-rectangle ∙
        (cancel-left target (pr₂ ◁ matching)) ⁻¹)
```
