# The two diagram coordinates of the insertion corner

The inner coordinate uses the normalized second insertion projection.
The outer coordinate uses the first projection after applying the outer
projection, then moves and normalizes its constant endpoint frame.
These are the component equations for comparing the boundary routes of
the square-currying permutation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.SquareDiagramCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public
import SCT.VolumeI.Chapter02.Section02.SquareInsertionCorner as Corner
import SCT.VolumeI.Chapter02.Section02.SquareInsertionNormalization as Normalize
import SCT.VolumeI.Chapter01.Section04.ProjectionSquares as Projections
open import SCT.VolumeI.Chapter01.Section04.SplitProjectionNaturality 𝒯 M using (section-natural)
open import SCT.VolumeI.Chapter01.Section04.SplitProjectionCalculus 𝒯 using (section-image)
open import SCT.VolumeI.Chapter01.Section08.ProjectionBaseCalculus 𝒯 using (change-middle)
module PS = Projections 𝒯

module OuterCoordinate (Γ A B : CAT) (u : Obj-abs A) (v : Obj-abs B) where
  module Input = Corner.At 𝒯 M ℱ Γ A B u v
  module Coordinates = Input.Coordinates
  module H = Input.H
  module V = Input.V
  ia = Input.ia
  ib = Input.ib
  χ = Input.corner
  ba = pair-β₁ (id Γ) (const u)
  bb = pair-β₂ (id Γ) (const v)
  module Source = Normalize.Incoming 𝒯 M ℱ ib u pr₂ bb
  module Target = Normalize.Outgoing 𝒯 M ℱ ib u (pr₂ {Γ} {B})
  gamma = Coordinates.outer
  identity-evaluation = section-image pr₁ ia ba (const v)
  middle-step = (bb ▷ pr₁) ∙ Target.first-step
  intermediate = PS.compose-base gamma V.step middle-step ia identity-evaluation
  source-frame = PS.compose-base gamma H.step (H.first-step pr₂) ib bb
  target-frame = PS.compose-base gamma V.step V.outer-step ia (const-pre v ia)

  abstract
    move-frame : intermediate =₂ (bb ∙ Target.normalized)
    move-frame = change-middle gamma V.step ia Target.first-step Target.at-endpoint
      (bb ▷ pr₁) identity-evaluation bb ((section-natural pr₁ ia ba bb) ⁻¹)

    remove-identity : target-frame =₂ intermediate
    remove-identity = isoComp-unitˡ-at intermediate ∙
      change-middle gamma V.step ia middle-step identity-evaluation (const-pre v pr₁) (const-pre v ia) (idIso (const v))
        (Normalize.ConstantSection.comparison 𝒯 M ℱ pr₁ ia ba v ∙ isoComp-unitˡ-at identity-evaluation)

    target-normalization : Input.outer-outgoing =₂ target-frame
    target-normalization = remove-identity ⁻¹ ∙ move-frame ⁻¹ ∙
      isoComp-cong (idIso bb) Target.comparison

    outer-square : PS.Square gamma source-frame target-frame χ
    outer-square = Source.comparison ∙ Input.outer-square ∙
      isoComp-cong (target-normalization ⁻¹) (idIso (gamma ◁ χ))

module InnerCoordinate (Γ A B : CAT) (u : Obj-abs A) (v : Obj-abs B) where
  module Input = Corner.At 𝒯 M ℱ Γ A B u v
  module Coordinates = Input.Coordinates
  module H = Input.H
  module V = Input.V
  module Insert = Input.Insert
  ia = Input.ia
  ib = Input.ib
  χ = Input.corner
  incoming = PS.compose-base Coordinates.inner H.step (pair-β₂ (id (Γ × B)) (const u)) ib (const-pre u ib)
  outgoing = PS.compose-base Coordinates.inner V.step V.inner-step ia (pair-β₂ (id Γ) (const u))

  inner-square : PS.Square Coordinates.inner incoming outgoing χ
  inner-square = Insert.normalized-projection₂
```
