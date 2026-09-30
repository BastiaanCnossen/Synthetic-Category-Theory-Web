# Postcomposition as a map of endpoint fibers

The image map built from the specified paired-evaluation square agrees
with the existing hom-post functor. We compare their complete endpoint
cones, including the terminal-leg normalization and matching, and lift
that comparison through the pullback universal property. Its whole image
computation is retained for use in later comparisons of hom squares.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomCalculus.HomFiberPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomPostcomposition 𝒯 M ℱ P I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (constant-image)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberExpressions as Expressions
import SCT.VolumeI.Chapter02.Section06.HomCalculus.FramedFiberImages as Images
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Lifting
open Laws.PullbackStructure P

module At {C D : CAT} (F : MAP C D) (x y : Obj-abs C) where
  private
    module Source = Expressions.Fiber 𝒯 M ℱ P I x y using (decode-encode)
    module Image = Images.Paired 𝒯 M ℱ P I F x y using (value; action; restrict; module At)

  source-cone = pullbackCone endpoints (pair x y)
  target-cone = pullbackCone endpoints (pair (F ∘ x) (F ∘ y))
  image-cone = Image.value source-cone
  image-map : MAP (Hom C x y) (Hom D (F ∘ x) (F ∘ y))
  image-map = pullbackLift image-cone
  image-map-computation : ConeIso (conePre image-map target-cone) image-cone
  image-map-computation = pullbackLift-β image-cone

  module Family {Γ : CAT} (h : MAP Γ (Hom C x y)) where
    normalized = EndpointFiber.cone x y (terminate Γ) (hom-expression h)
    hom-image-cone = EndpointFiber.cone (F ∘ x) (F ∘ y) (terminate Γ) (hom-image F (hom-expression h))
    private
      module Normal = Image.At normalized using (post-image; cone-comparison)

    expression-comparison : ExpressionIso Normal.post-image (hom-image F (hom-expression h))
    expression-comparison = retarget-expressionIso
      (post-expressionIso F (Source.decode-encode (terminate Γ) (hom-expression h)))
      (constant-image Γ F x) (constant-image Γ F y)

    normalized-comparison : ConeIso (Image.value normalized) hom-image-cone
    normalized-comparison = coneIso-compose
      (EncodeComparison.comparison (F ∘ x) (F ∘ y) (terminate Γ) expression-comparison)
      Normal.cone-comparison

    image-comparison : ConeIso (Image.value (conePre h source-cone)) hom-image-cone
    image-comparison = coneIso-compose normalized-comparison (Image.action (Normalize.comparison h))

    post-comparison : ConeIso (conePre (hom-post F x y ∘ h) target-cone)
      (Image.value (conePre h source-cone))
    post-comparison = coneIso-compose (coneIso-inverse image-comparison)
      (coneIso-compose
        (EncodeComparison.comparison (F ∘ x) (F ∘ y) (terminate Γ) (hom-post-β F x y h))
        (Normalize.comparison (hom-post F x y ∘ h)))

  private
    module Universal = Family (id (Hom C x y)) using (image-comparison)
  post-comparison : ConeIso (conePre (hom-post F x y) target-cone) image-cone
  post-comparison = coneIso-compose (Image.action (conePre-id source-cone))
    (coneIso-compose (coneIso-inverse Universal.image-comparison)
      (coneIso-compose
        (EncodeComparison.comparison (F ∘ x) (F ∘ y) (terminate (Hom C x y))
          (hom-post-computation F x y))
        (Normalize.comparison (hom-post F x y))))

  prescribed : ConeIso (conePre image-map target-cone) (conePre (hom-post F x y) target-cone)
  prescribed = coneIso-compose (coneIso-inverse post-comparison) image-map-computation
  private
    module LiftedComparison = Lifting.Lift 𝒯 P image-map (hom-post F x y) prescribed
      using (lift; comparison-image; left-image; right-image)
  open LiftedComparison public using (comparison-image; left-image; right-image) renaming (lift to comparison)
```
