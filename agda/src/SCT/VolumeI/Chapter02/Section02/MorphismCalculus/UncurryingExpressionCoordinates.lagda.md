# Coordinates of evaluation after uncurrying

The evaluation presentation of an uncurried transformation has a product
of two diagrams. Exchanging the interval and domain coordinates identifies
it with double uncurrying. This module supplies that diagram comparison;
compatibility with specified transformation endpoints is a separate step.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressionCoordinates
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.NestedSymmetry as Symmetry

module Coordinates (Γ X : CAT) where
  module Swap = Symmetry.At 𝒯 Γ [1] X
  permutation = Swap.forward
  step : MAP ((Γ × X) × [1]) (Γ × [1])
  step = productMap pr₁ (id [1])
  fixed : MAP (Γ × X) X
  fixed = id X ∘ pr₂
  step-comparison : (step ∘ permutation) =₁ pr₁
  step-comparison = pair-η pr₁ ∙
    (pair-cong Swap.parameter
      (comp-unitˡ (pr₂ ∘ pr₁) ∙ ((id [1] ◁ Swap.last) ∙ comp-assoc permutation pr₂ (id [1]))) ∙
      pair-pre (pr₁ ∘ pr₁) (id [1] ∘ pr₂) permutation)

  second : ((fixed ∘ pr₁) ∘ permutation) =₁ (id X ∘ pr₂)
  second = (id X ◁ Swap.inner) ∙
    (comp-assoc permutation (pr₂ ∘ pr₁) (id X) ∙
      (comp-assoc pr₁ pr₂ (id X) ▷ permutation))

module At (Γ X C : CAT) (h : MAP Γ (Ar (Fun X C))) where
  open Coordinates Γ X public
  H = funUncurry h
  paired : MAP ((Γ × X) × [1]) (Fun X C × X)
  paired = pair (H ∘ step) (fixed ∘ pr₁)
  diagram : MAP ((Γ × X) × [1]) C
  diagram = funEval ∘ paired

  first : ((H ∘ step) ∘ permutation) =₁ (H ∘ pr₁)
  first = (H ◁ step-comparison) ∙ comp-assoc permutation step H

  paired-comparison : (paired ∘ permutation) =₁ productMap H (id X)
  paired-comparison = pair-cong first second ∙ pair-pre (H ∘ step) (fixed ∘ pr₁) permutation

  comparison : (diagram ∘ permutation) =₁ funUncurry H
  comparison = (funEval ◁ paired-comparison) ∙ comp-assoc permutation paired funEval
```
