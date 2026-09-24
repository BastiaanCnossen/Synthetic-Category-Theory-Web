# The parameter coordinate of the square corner

The two boundary routes of the currying permutation preserve the same
parameter frame. This uses the actual axis projection witnesses and
the insertion corner, with their units and associators normalized.
The two diagram-coordinate equations are separate obligations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.SquareParameterCorner
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

module At (Γ A B : CAT) (u : Obj-abs A) (v : Obj-abs B) where
  module Input = Corner.At 𝒯 M ℱ Γ A B u v
  module Coordinates = Input.Coordinates
  module H = Input.H
  module V = Input.V
  ia = Input.ia
  ib = Input.ib
  χ = Input.corner
  ba = pair-β₁ (id Γ) (const u)
  bb = pair-β₁ (id Γ) (const v)
  module Source = Normalize.Incoming 𝒯 M ℱ ib u pr₁ bb
  module Target = Normalize.Outgoing 𝒯 M ℱ ib u (pr₁ {Γ} {B})
  gamma = Coordinates.parameter
  J = Coordinates.permute
  betaJ = pair-β₁ Coordinates.parameter Coordinates.rectangle
  identity-evaluation = section-image pr₁ ia ba (id Γ)
  middle-step = (bb ▷ pr₁) ∙ Target.first-step
  intermediate = PS.compose-base gamma V.step middle-step ia identity-evaluation
  source-frame = PS.compose-base gamma H.step (H.first-step pr₁) ib bb
  target-frame = PS.compose-base gamma V.step V.parameter-step ia ba

  abstract
    move-frame : intermediate =₂ (bb ∙ Target.normalized)
    move-frame = change-middle gamma V.step ia Target.first-step Target.at-endpoint
      (bb ▷ pr₁) identity-evaluation bb ((section-natural pr₁ ia ba bb) ⁻¹)

    remove-identity : target-frame =₂ intermediate
    remove-identity = isoComp-unitˡ-at intermediate ∙
      change-middle gamma V.step ia middle-step identity-evaluation (comp-unitˡ pr₁) ba (idIso (id Γ))
        (Normalize.identity-section 𝒯 M ℱ pr₁ ia ba ∙ isoComp-unitˡ-at identity-evaluation)

    target-normalization : Input.parameter-outgoing =₂ target-frame
    target-normalization = remove-identity ⁻¹ ∙ move-frame ⁻¹ ∙
      isoComp-cong (idIso bb) Target.comparison

    parameter-square : PS.Square gamma source-frame target-frame χ
    parameter-square = Source.comparison ∙ Input.parameter-square ∙
      isoComp-cong (target-normalization ⁻¹) (idIso (gamma ◁ χ))

  -- The axis-induced matching retains the parameter coordinate.
  source = PS.compose-base pr₁ H.restriction H.target-first ib bb
  target = PS.compose-base pr₁ V.restriction V.target-first ia ba
  stage₁ = PS.compose-base pr₁ (J ∘ H.step) H.source-first ib bb
  stage₂ = PS.compose-base pr₁ J betaJ (H.step ∘ ib) source-frame
  stage₃ = PS.compose-base pr₁ J betaJ (V.step ∘ ia) target-frame
  stage₄ = PS.compose-base pr₁ (J ∘ V.step) V.source-first ia ba
  first = (H.comparison ▷ ib) ⁻¹
  second = comp-assoc ib H.step J
  third = J ◁ χ
  fourth = (comp-assoc ia V.step J) ⁻¹
  fifth = V.comparison ▷ ia

  matching : (H.restriction ∘ ib) =₁ (V.restriction ∘ ia)
  matching = fifth ∙ (fourth ∙ (third ∙ (second ∙ first)))

  abstract
    matching-parameter : PS.Square pr₁ source target matching
    matching-parameter = PS.compose-square pr₁ source stage₄ target fifth _
      (PS.pre-square pr₁ ia V.source-first V.target-first ba V.comparison V.projection₁)
      (PS.compose-square pr₁ source stage₃ stage₄ fourth _
        (PS.inverse-square pr₁ stage₄ stage₃ (comp-assoc ia V.step J)
          (PS.associator-square pr₁ J V.step ia betaJ V.parameter-step ba))
        (PS.compose-square pr₁ source stage₂ stage₃ third _
          (PS.post-square pr₁ J betaJ source-frame target-frame χ parameter-square)
          (PS.compose-square pr₁ source stage₁ stage₂ second first
            (PS.associator-square pr₁ J H.step ib betaJ (H.first-step pr₁) bb)
            (PS.inverse-square pr₁ stage₁ source (H.comparison ▷ ib)
              (PS.pre-square pr₁ ib H.source-first H.target-first bb H.comparison H.projection₁)))))
```
