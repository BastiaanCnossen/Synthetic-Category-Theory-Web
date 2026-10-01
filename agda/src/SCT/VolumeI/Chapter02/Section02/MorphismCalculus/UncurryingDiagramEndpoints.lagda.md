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

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionDiagramPresentations as Presentations
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressionCoordinates as Coordinates
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EvaluatedUncurryingEndpoints as Evaluated
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.RestrictedFrames as Frames
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointNaturality 𝒯 M ℱ
  using (application-natural)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
-- Restructured: no module instantiations except record modules; results of
-- other modules are used as ordinary functions with explicit arguments.
module At {Γ X C : CAT} {f g : MAP Γ (Fun X C)} (α : MorphismExpression f g) where
  module A = MorphismExpression α
    using (arrow; source-frame; target-frame)
  uncurried = post-expression funEval
    (pair-expression (restrict-expression α pr₁) (identity-expression (id X ∘ pr₂)))
  module B = MorphismExpression uncurried
  private
    W = Presentations.Evaluation.value 𝒯 M ℱ P I E α
    diagram = Presentations.Presentation.diagram W
    W-comparison = Presentations.Presentation.comparison W
    H = Coordinates.At.H 𝒯 M ℱ I Γ X C A.arrow
    permutation = Coordinates.At.permutation 𝒯 M ℱ I Γ X C A.arrow
    coordinate = Coordinates.At.comparison 𝒯 M ℱ I Γ X C A.arrow
  original : MAP ((Γ × X) × [1]) C
  original = funUncurry B.arrow
  comparison : (original ∘ permutation) =₁ funUncurry H
  comparison = coordinate ∙ (W-comparison ▷ permutation)

  module Endpoint (z : Obj-abs [1]) {h : MAP Γ (Fun X C)}
    (a : (evaluate z ∘ A.arrow) =₁ h)
    (front : (original ∘ insert z) =₁ funUncurry h) where
    p : (H ∘ insert z) =₁ h
    p = a ∙ (evaluate-uncurry z A.arrow) ⁻¹
    private
      i = Evaluated.At.Endpoint.J.i 𝒯 M ℱ I Γ X C A.arrow z p
      j = Evaluated.At.Endpoint.J.j 𝒯 M ℱ I Γ X C A.arrow z p
      s = Evaluated.At.Endpoint.J.s 𝒯 M ℱ I Γ X C A.arrow z p
      κ = Evaluated.At.Endpoint.J.κ 𝒯 M ℱ I Γ X C A.arrow z p
      V-frame = Evaluated.At.Endpoint.frame 𝒯 M ℱ I Γ X C A.arrow z p
      V-comparison = Evaluated.At.Endpoint.comparison 𝒯 M ℱ I Γ X C A.arrow z p
      normal = Frames.At.comparison 𝒯 M ℱ H (insert z) p
    R : (funUncurry H ∘ s) =₁ funUncurry h
    R = funUncurryIso p ∙ (funUncurry-restrict H i) ⁻¹
    before : ((original ∘ permutation) ∘ s) =₁ (original ∘ j)
    before = (original ◁ κ) ∙ comp-assoc s permutation original
    after : ((diagram ∘ permutation) ∘ s) =₁ (diagram ∘ j)
    after = (diagram ◁ κ) ∙ comp-assoc s permutation diagram
    δ : ((original ∘ permutation) ∘ s) =₁ ((diagram ∘ permutation) ∘ s)
    δ = (W-comparison ▷ permutation) ▷ s

    abstract
      evaluated : (R ∙ (coordinate ▷ s)) =₂ (V-frame ∙ after)
      evaluated = V-comparison ⁻¹ ∙
        isoComp-cong normal (idIso (coordinate ▷ s))

      compatible : (V-frame ∙ (W-comparison ▷ j)) =₂ front →
        (R ∙ (comparison ▷ s)) =₂ (front ∙ before)
      compatible same = isoComp-cong same (idIso before) ∙
        (isoComp-assoc-at V-frame (W-comparison ▷ j) before) ⁻¹ ∙
        isoComp-cong (idIso V-frame) (application-natural permutation s κ W-comparison) ∙
        isoComp-assoc-at V-frame after δ ∙
        isoComp-cong evaluated (idIso δ) ∙
        (isoComp-assoc-at R (coordinate ▷ s) δ) ⁻¹ ∙
        isoComp-cong (idIso R)
          (preWhisker-isoComp-at coordinate (W-comparison ▷ permutation) s)

  source-compatible = Endpoint.compatible zero A.source-frame
    (B.source-frame ∙ (evaluate-uncurry zero B.arrow) ⁻¹)
    (Presentations.Presentation.source-compatible W)
  target-compatible = Endpoint.compatible one A.target-frame
    (B.target-frame ∙ (evaluate-uncurry one B.arrow) ⁻¹)
    (Presentations.Presentation.target-compatible W)
```
