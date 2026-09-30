# Frames of a product image family

The specified productMap-pair comparison identifies the image of a paired
family with the pair of its images. Its two coordinate frames, after
restriction, are the images of the original projection frames followed by
the inverse associators. These are computations of the selected comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section06.Coordinates.ProductFamilyFrames
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductPairing
  vocabulary terminal products productLaws composition vertical whiskering using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductCones as Products
import SCT.VolumeI.Chapter01.Section06.Coordinates.FramedProjectionRestriction as Frames

module Paired {B C₀ C₁ D₀ D₁ : CAT} (F : MAP C₀ D₀) (G : MAP C₁ D₁)
  (x : MAP B C₀) (y : MAP B C₁) where
  private
    module Product = Products.Coordinates 𝒯 F G F G using (module First; module Second)
  family = pair x y
  target = pair (F ∘ x) (G ∘ y)
  δ = productMap-pair F G x y

  abstract
    first-triangle : (pair-β₁ (F ∘ x) (G ∘ y) ∙ (pr₁ ◁ δ)) =₂
      ((F ◁ pair-β₁ x y) ∙ Product.First.left-normal family)
    first-triangle = isoComp-assoc-at (F ◁ pair-β₁ x y) (comp-assoc family pr₁ F)
        ((pair-β₁ (F ∘ pr₁) (G ∘ pr₂) ▷ family) ∙ (comp-assoc family (productMap F G) pr₁) ⁻¹) ∙
      pair-pre-cong-triangle₁ (F ∘ pr₁) (G ∘ pr₂) family
        ((F ◁ pair-β₁ x y) ∙ comp-assoc family pr₁ F)
        ((G ◁ pair-β₂ x y) ∙ comp-assoc family pr₂ G)
    second-triangle : (pair-β₂ (F ∘ x) (G ∘ y) ∙ (pr₂ ◁ δ)) =₂
      ((G ◁ pair-β₂ x y) ∙ Product.Second.left-normal family)
    second-triangle = isoComp-assoc-at (G ◁ pair-β₂ x y) (comp-assoc family pr₂ G)
        ((pair-β₂ (F ∘ pr₁) (G ∘ pr₂) ▷ family) ∙ (comp-assoc family (productMap F G) pr₂) ⁻¹) ∙
      pair-pre-cong-triangle₂ (F ∘ pr₁) (G ∘ pr₂) family
        ((F ◁ pair-β₁ x y) ∙ comp-assoc family pr₁ F)
        ((G ◁ pair-β₂ x y) ∙ comp-assoc family pr₂ G)
  private
    module First = Frames.AlongIdentification 𝒯 pr₁ (productMap F G) pr₁ F
      (pair-β₁ (F ∘ pr₁) (G ∘ pr₂)) family (pair-β₁ x y)
      target (pair-β₁ (F ∘ x) (G ∘ y)) δ using (module Restrict)
    module Second = Frames.AlongIdentification 𝒯 pr₂ (productMap F G) pr₂ G
      (pair-β₂ (F ∘ pr₁) (G ∘ pr₂)) family (pair-β₂ x y)
      target (pair-β₂ (F ∘ x) (G ∘ y)) δ using (module Restrict)

  module At {Γ : CAT} (r : MAP Γ B) where
    family-change = (δ ▷ r) ∙ (comp-assoc r family (productMap F G)) ⁻¹
    source-change = project-pair₁ (F ∘ x) (G ∘ y) r ∙
      ((pr₁ ◁ family-change) ∙ (Product.First.left-normal (family ∘ r)) ⁻¹)
    target-change = project-pair₂ (F ∘ x) (G ∘ y) r ∙
      ((pr₂ ◁ family-change) ∙ (Product.Second.left-normal (family ∘ r)) ⁻¹)

    source-computation : source-change =₂ ((comp-assoc r x F) ⁻¹ ∙ (F ◁ project-pair₁ x y r))
    source-computation = First.Restrict.comparison first-triangle r
    target-computation : target-change =₂ ((comp-assoc r y G) ⁻¹ ∙ (G ◁ project-pair₂ x y r))
    target-computation = Second.Restrict.comparison second-triangle r
```
