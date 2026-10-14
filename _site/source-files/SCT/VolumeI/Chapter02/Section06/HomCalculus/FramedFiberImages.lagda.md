# Expressing framed images of endpoint fibers

An arbitrary endpoint family need not be a literal pair of functors.
Decode its two projected matching equations before postcomposing. A
specified identification of the image family with a target pair then
retargets the resulting morphism expression.

The comparison below identifies the whole image cone with the cone of
that expression. Both endpoint changes are displayed explicitly. Their
further simplification, and comparison with the chosen `hom-post` functor,
remain separate calculations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomCalculus.FramedFiberImages
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts 𝒯 M ℱ P I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (same-arrow; retarget-cong; retarget-assoc; post-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-boundary-normal)
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.PairedEvaluationImages as Images
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductCones as Products
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductFamilyFrames as FamilyFrames
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductPairing
  vocabulary terminal products productLaws composition vertical whiskering using (productMap-pair)

module Along {B C D : CAT} (F : MAP C D) (family : MAP B (C × C))
  (u v : MAP B D) (δ : (productMap F F ∘ family) =₁ pair u v) where
  private
    module Image = Images.Along 𝒯 M ℱ zero one F family (pair u v) δ
      using (value; action; restrict; right-normal; first-boundary; second-boundary)
    module Product = Products.Coordinates 𝒯 F F F F using (module First; module Second)
    module Target = Fiber u v using (decode; encode-decode)
    module TargetLifts = Lifts u v using (encode-cong)

  open Image public using (value; action; restrict)

  module At {Γ : CAT} (q : Cone endpoints family Γ) where
    raw : MorphismExpression (pr₁ ∘ (family ∘ Cone.right q)) (pr₂ ∘ (family ∘ Cone.right q))
    raw = record
      { arrow = Cone.left q
      ; source-frame = (pr₁ ◁ Cone.match q) ∙ (project-pair₁ ev₀ ev₁ (Cone.left q)) ⁻¹
      ; target-frame = (pr₂ ◁ Cone.match q) ∙ (project-pair₂ ev₀ ev₁ (Cone.left q)) ⁻¹ }

    source-change : (F ∘ (pr₁ ∘ (family ∘ Cone.right q))) =₁ (u ∘ Cone.right q)
    source-change = project-pair₁ u v (Cone.right q) ∙
      ((pr₁ ◁ Image.right-normal (Cone.right q)) ∙
        (Product.First.left-normal (family ∘ Cone.right q)) ⁻¹)
    target-change : (F ∘ (pr₂ ∘ (family ∘ Cone.right q))) =₁ (v ∘ Cone.right q)
    target-change = project-pair₂ u v (Cone.right q) ∙
      ((pr₂ ◁ Image.right-normal (Cone.right q)) ∙
        (Product.Second.left-normal (family ∘ Cone.right q)) ⁻¹)

    image-expression : MorphismExpression (u ∘ Cone.right q) (v ∘ Cone.right q)
    image-expression = retarget-expression (post-expression F raw) source-change target-change

    expression-comparison : ExpressionIso (Target.decode (value q)) image-expression
    expression-comparison = same-arrow (funPost F ∘ Cone.left q) _ _ _ _ source-computation target-computation
      where
      abstract
        source-computation : MorphismExpression.source-frame image-expression =₂
          MorphismExpression.source-frame (Target.decode (value q))
        source-computation = isoComp-cong (idIso (project-pair₁ u v (Cone.right q)))
            ((Image.first-boundary q) ⁻¹) ∙
          (isoComp-assoc-at (project-pair₁ u v (Cone.right q))
            ((pr₁ ◁ Image.right-normal (Cone.right q)) ∙
              (Product.First.left-normal (family ∘ Cone.right q)) ⁻¹)
            ((F ◁ MorphismExpression.source-frame raw) ∙ evaluate-post-at zero F (Cone.left q)) ∙
            isoComp-cong (idIso source-change)
              (post-boundary-normal zero F (Cone.left q) (MorphismExpression.source-frame raw)))
        target-computation : MorphismExpression.target-frame image-expression =₂
          MorphismExpression.target-frame (Target.decode (value q))
        target-computation = isoComp-cong (idIso (project-pair₂ u v (Cone.right q)))
            ((Image.second-boundary q) ⁻¹) ∙
          (isoComp-assoc-at (project-pair₂ u v (Cone.right q))
            ((pr₂ ◁ Image.right-normal (Cone.right q)) ∙
              (Product.Second.left-normal (family ∘ Cone.right q)) ⁻¹)
            ((F ◁ MorphismExpression.target-frame raw) ∙ evaluate-post-at one F (Cone.left q)) ∙
            isoComp-cong (idIso target-change)
              (post-boundary-normal one F (Cone.left q) (MorphismExpression.target-frame raw)))

    cone-comparison : ConeIso (value q) (EndpointFiber.cone u v (Cone.right q) image-expression)
    cone-comparison = coneIso-compose (TargetLifts.encode-cong (Cone.right q) expression-comparison)
      (Target.encode-decode (value q))
```


For a paired source family, the chosen product comparison normalizes both
endpoint changes. The result is postcomposition of the decoded expression,
with its endpoints reassociated over the same base parameter.

```agda
module Paired {B C D : CAT} (F : MAP C D) (x y : MAP B C) where
  private
    module General = Along F (pair x y) (F ∘ x) (F ∘ y) (productMap-pair F F x y)
      using (value; action; restrict; module At)
    module Source = Fiber x y using (decode)
    module Target = Lifts (F ∘ x) (F ∘ y) using (encode-cong)
    module Frames = FamilyFrames.Paired 𝒯 F F x y using (module At)
  open General public using (value; action; restrict)

  module At {Γ : CAT} (q : Cone endpoints (pair x y) Γ) where
    private
      module Image = General.At q using (raw; image-expression; cone-comparison)
      module Frame = Frames.At (Cone.right q) using (source-computation; target-computation)

    post-image : MorphismExpression ((F ∘ x) ∘ Cone.right q) ((F ∘ y) ∘ Cone.right q)
    post-image = retarget-expression (post-expression F (Source.decode q))
      ((comp-assoc (Cone.right q) x F) ⁻¹) ((comp-assoc (Cone.right q) y F) ⁻¹)

    expression-comparison : ExpressionIso Image.image-expression post-image
    expression-comparison = expressionIso-compose
      (retarget-expressionIso (expressionIso-inverse (post-retarget F Image.raw
        (project-pair₁ x y (Cone.right q)) (project-pair₂ x y (Cone.right q))))
        ((comp-assoc (Cone.right q) x F) ⁻¹) ((comp-assoc (Cone.right q) y F) ⁻¹))
      (expressionIso-compose
        (expressionIso-inverse (retarget-assoc (post-expression F Image.raw)
          (F ◁ project-pair₁ x y (Cone.right q)) (F ◁ project-pair₂ x y (Cone.right q))
          ((comp-assoc (Cone.right q) x F) ⁻¹) ((comp-assoc (Cone.right q) y F) ⁻¹)))
        (retarget-cong (post-expression F Image.raw) Frame.source-computation Frame.target-computation))

    cone-comparison : ConeIso (value q)
      (EndpointFiber.cone (F ∘ x) (F ∘ y) (Cone.right q) post-image)
    cone-comparison = coneIso-compose (Target.encode-cong (Cone.right q) expression-comparison)
      Image.cone-comparison
```
