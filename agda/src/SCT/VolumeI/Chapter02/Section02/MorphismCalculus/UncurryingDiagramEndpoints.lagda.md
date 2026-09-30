# Exchanged uncurrying with its endpoint frames

The evaluation presentation and the coordinate exchange identify the
uncurried expression diagram with the iterated uncurrying of the original
arrow. Both endpoint equations are retained. These equations are needed
before reflecting the comparison through currying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingDiagramEndpoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionDiagramPresentations as Presentations
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressionCoordinates as Coordinates
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EvaluatedUncurryingEndpoints as Evaluated
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.RestrictedFrames as Frames
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointNaturality 𝒯 M ℱ
  using (application-natural)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
module Presentation = Presentations 𝒯 M ℱ P I E

module At {Γ X C : CAT} {f g : MAP Γ (Fun X C)} (α : MorphismExpression f g) where
  module A = MorphismExpression α
  uncurried = post-expression funEval
    (pair-expression (restrict-expression α pr₁) (identity-expression (id X ∘ pr₂)))
  module B = MorphismExpression uncurried
  module W = Presentation.Presentation (Presentation.Evaluation.value α)
  module Coordinate = Coordinates.At 𝒯 M ℱ I Γ X C A.arrow
  open Coordinate using (H; permutation)
  original : MAP ((Γ × X) × [1]) C
  original = funUncurry B.arrow
  comparison : (original ∘ permutation) =₁ funUncurry H
  comparison = Coordinate.comparison ∙ (W.comparison ▷ permutation)

  module Endpoint (z : Obj-abs [1]) {h : MAP Γ (Fun X C)}
    (a : (evaluate z ∘ A.arrow) =₁ h)
    (front : (original ∘ insert z) =₁ funUncurry h) where
    p : (H ∘ insert z) =₁ h
    p = a ∙ (evaluate-uncurry z A.arrow) ⁻¹
    module V = Evaluated.At.Endpoint 𝒯 M ℱ I Γ X C A.arrow z p
    module Normal = Frames.At 𝒯 M ℱ H (insert z) p
    open V.J using (i; j; s; κ)
    R : (funUncurry H ∘ s) =₁ funUncurry h
    R = funUncurryIso p ∙ (funUncurry-restrict H i) ⁻¹
    before : ((original ∘ permutation) ∘ s) =₁ (original ∘ j)
    before = (original ◁ κ) ∙ comp-assoc s permutation original
    after : ((W.diagram ∘ permutation) ∘ s) =₁ (W.diagram ∘ j)
    after = (W.diagram ◁ κ) ∙ comp-assoc s permutation W.diagram
    δ : ((original ∘ permutation) ∘ s) =₁ ((W.diagram ∘ permutation) ∘ s)
    δ = (W.comparison ▷ permutation) ▷ s

    abstract
      evaluated : (R ∙ (Coordinate.comparison ▷ s)) =₂ (V.frame ∙ after)
      evaluated = V.comparison ⁻¹ ∙
        isoComp-cong Normal.comparison (idIso (Coordinate.comparison ▷ s))

      compatible : (V.frame ∙ (W.comparison ▷ j)) =₂ front →
        (R ∙ (comparison ▷ s)) =₂ (front ∙ before)
      compatible same = isoComp-cong same (idIso before) ∙
        (isoComp-assoc-at V.frame (W.comparison ▷ j) before) ⁻¹ ∙
        isoComp-cong (idIso V.frame) (application-natural permutation s κ W.comparison) ∙
        isoComp-assoc-at V.frame after δ ∙
        isoComp-cong evaluated (idIso δ) ∙
        (isoComp-assoc-at R (Coordinate.comparison ▷ s) δ) ⁻¹ ∙
        isoComp-cong (idIso R)
          (preWhisker-isoComp-at Coordinate.comparison (W.comparison ▷ permutation) s)

  module Source = Endpoint zero A.source-frame (B.source-frame ∙ (evaluate-uncurry zero B.arrow) ⁻¹)
  module Target = Endpoint one A.target-frame (B.target-frame ∙ (evaluate-uncurry one B.arrow) ⁻¹)

  source-compatible = Source.compatible W.source-compatible
  target-compatible = Target.compatible W.target-compatible
```
