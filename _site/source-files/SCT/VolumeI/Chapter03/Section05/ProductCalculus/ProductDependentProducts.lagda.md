# Dependent products along product projections

This proves the dependent-product assertion in
`prop:map_to_the_point_is exponentiable`. The category is the manuscript's
pullback of `Fun(S,E)` along the family of fibers. Its evaluation is the
specified uncurried evaluation transported to the chosen pullback domain.
The preceding family comparison proves the literal uncurrying map is an
equivalence, and taking cores gives its mapping-anima universal property.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductDependentProducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductDependentUncurrying 𝒯 M ℱ P using (module Uncurrying)

module AlongProjection {T S E : CAT} (r : MAP E (T × S)) where
  module U = Uncurrying r
  module Ev = U.Ev

  module At {K : CAT} (k : MAP K T) where
    module F = U.At k
    uncurrying = EvaluationAlong.uncurrying Ev.F.projection r Ev.projection Ev.evaluation k
    abstract
      core-comparison : uncurrying =₁ mapPost F.functor
      core-comparison = mapPost-comp F.BC.functor F.Post.functor ∙
        ((mapPost F.Post.functor ◁ F.BC.maps-as-core) ∙ (F.Post.maps-as-core ▷ F.BC.maps))
      isEquiv : IsEquiv uncurrying
      isEquiv = equiv-transport (core-comparison ⁻¹) (mapPost-isEquiv F.functor F.functor-isEquiv)

  abstract
    universal : IsDependentProduct Ev.F.projection r Ev.projection Ev.evaluation
    universal = record { universal = At.isEquiv }

  dependent-product : DependentProduct (pr₁ {T} {S}) r
  dependent-product = record { category = Ev.category ; projection = Ev.projection
    ; evaluation = Ev.evaluation ; isDependentProduct = universal }
```
