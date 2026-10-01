# Fixing the source of directed evaluation

The fiber of the comma category over `x` is the coslice at `p x`.
Cancelling this pullback against the source-endpoint presentation of
`C_{x/}` gives a pullback square for directed evaluation with source
fixed. Both universal factorizations retain their complete cone data.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.SourceRestrictedEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter04.Section01.EvaluationCalculus.EndpointPullbacks 𝒯 M ℱ P I
  using (module Source; module Evaluation)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; conePre; IsPullback; module UniversalCone)
open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I
  using (module Criterion)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; coneIso-pre)
import SCT.VolumeI.Chapter04.Section03.CosliceFunctors as CosliceFunctors
import SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeConeRecovery as Recovery
import SCT.VolumeI.Chapter01.Section06.Cospans.SquareSubstitution as Substitution
import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction as Action
import SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeSquares as BaseChange
import SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonCancellation as Cancellation

module At {C D : CAT} (p : MAP C D) (x : Obj-abs C) where
  private
    module Comma = Source p using (square; square-isPullback)
    module Eval = Evaluation p using (module Left; directed-ev₀; directed-ev₀-base)
    module Cx = CosliceEndpoint x using (square; square-isPullback)
    module Dx = CosliceEndpoint (p ∘ x) using (square; square-isPullback)
    module Fiber = BaseChange.Along 𝒯 P ev₀ p Comma.square Comma.square-isPullback
      x (idIso (p ∘ x)) Dx.square Dx.square-isPullback
      using (factor; factor-computation; factor-cone; square; square-isPullback)

  inclusion : MAP (Coslice D (p ∘ x)) Eval.Left.category
  inclusion = Fiber.factor

  fiber-square : Cone (Cone.right Comma.square) x (Coslice D (p ∘ x))
  fiber-square = Fiber.square

  fiber-square-isPullback : IsPullback fiber-square
  fiber-square-isPullback = Fiber.square-isPullback

  inclusion-cone = Fiber.factor-cone
  inclusion-computation = Fiber.factor-computation

  private
    source-frame : (Cone.right Comma.square ∘ Eval.directed-ev₀) =₁ ev₀
    source-frame = ConeIso.rightIso (Criterion.source-comparison p)
    module Cancel = Cancellation.Framed 𝒯 P Eval.directed-ev₀ (Cone.right Comma.square) x
      source-frame fiber-square fiber-square-isPullback Cx.square Cx.square-isPullback
      using (edge-cone; module WithComparison)
    module Target = UniversalCone fiber-square fiber-square-isPullback using (factor; factor-β)

  evaluation : MAP (Coslice C x) (Coslice D (p ∘ x))
  evaluation = Target.factor Cancel.edge-cone

  computation : ConeIso (conePre evaluation fiber-square) Cancel.edge-cone
  computation = Target.factor-β Cancel.edge-cone

  private
    module Result = Cancel.WithComparison evaluation computation using (square; square-isPullback)

  square : Cone Eval.directed-ev₀ inclusion (Coslice C x)
  square = Result.square

  square-isPullback : IsPullback square
  square-isPullback = Result.square-isPullback

  private
    module Recover = Recovery.Along 𝒯 P ev₀ p Comma.square Comma.square-isPullback
      x Dx.square Dx.square-isPullback using (cospan; comparison)
    module Substitute = Substitution.At 𝒯 P ev₀ p Comma.square Eval.directed-ev₀
      (Criterion.source-square p) (Criterion.source-comparison p) x Cx.square
      using (comparison)
    module Map = Action.Action 𝒯 P Recover.cospan using (map-iso; map-pre)
    module Image = CosliceFunctors.Image 𝒯 M ℱ P I p x using (functor; image; computation)
    module Endpoint = UniversalCone Dx.square Dx.square-isPullback using (reflect)

  abstract
    endpoint-computation : ConeIso (conePre evaluation Dx.square) Image.image
    endpoint-computation = coneIso-compose Substitute.comparison
      (coneIso-compose (Map.map-iso computation)
      (coneIso-compose (coneIso-inverse (Map.map-pre evaluation fiber-square))
        (coneIso-inverse (coneIso-pre evaluation Recover.comparison))))

    evaluation-comparison : evaluation =₁ Image.functor
    evaluation-comparison = Endpoint.reflect evaluation Image.functor
      (coneIso-compose (coneIso-inverse Image.computation) endpoint-computation)
```
