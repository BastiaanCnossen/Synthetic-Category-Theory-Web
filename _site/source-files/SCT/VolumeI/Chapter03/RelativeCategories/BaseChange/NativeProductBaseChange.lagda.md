# Product base change and the chosen pullback lift

The product triangle induces the same functor into the chosen pullback
as lifting the cone obtained by acting on the product square. The cone
comparison retains exactly the right-leg identification used by the
relative functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.NativeProductBaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductSquares 𝒯 P using (module FirstFactor)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.RestrictedConeLifts 𝒯 M ℱ P using (module Restriction)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductDependentEvaluation 𝒯 M ℱ P using (module Fibers)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductUncurryingTriangles 𝒯 M ℱ P using (module Product)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ProductTriangleCones 𝒯 M ℱ P using (module Triangle)

module BaseChange {K G T : CAT} (S : CAT) {k : MAP K T} {g : MAP G T}
  (u : FunctorOver k g) where
  module F = Fibers T S
  module C = Triangle S u
  source = compose-over (F.Domain.inclusion g) (Product.value S u)
  target = lift-triangle (Action.value F.projection u (FirstFactor.square k S))

  abstract
    comparison : FunctorOverIso source target
    comparison = Restriction.comparison (FirstFactor.square g S) C.target (Product.value S u)
      C.comparison C.right-image
```
