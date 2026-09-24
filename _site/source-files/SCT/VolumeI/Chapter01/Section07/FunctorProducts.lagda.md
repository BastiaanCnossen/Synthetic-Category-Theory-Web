# Functor categories preserve products

For `lem:FunctorCategoryIntoProduct`, test the specified pair of
postcomposition functors on `Map T`. Uncurrying on the source and both
target factors identifies it with the mapping-anima product comparison.
Every arrow in that comparison is an equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.Currying as Currying
import SCT.VolumeI.Chapter01.Section07.Functoriality as Functoriality

import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.FunctorProducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Currying 𝒯 M F
open Functoriality 𝒯 M F
open import SCT.VolumeI.Chapter01.Section07.MappingTests 𝒯 M F
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (post-tests-all)
import SCT.VolumeI.Chapter01.Section04.MappingProducts as MappingProducts
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯
  using (productMap-isEquiv; pair-after)

module ProductComparison (E C D : CAT) where
  Source = Fun E (C × D)
  Target = Fun E C × Fun E D

  forward : MAP Source Target
  forward = pair (funPost pr₁) (funPost pr₂)
```

For a test category `T`, both routes land in
`Map (T × E) C × Map (T × E) D`. The square is an identification of
functors on the entire mapping anima, proved by the two postcomposition
comparisons. Cancellation then proves the actual `mapPost forward` is
an equivalence.

```agda
  module OnMaps (T : CAT) where
    module SourceProduct = MappingProducts.ProductComparison 𝒯 M (T × E) C D
    module TargetProduct = MappingProducts.ProductComparison 𝒯 M T (Fun E C) (Fun E D)
    module UC = Test T E C
    module UD = Test T E D
    module UCD = Test T E (C × D)

    targetComparison = productMap UC.forward UD.forward ∘ TargetProduct.forward
    sourceComparison = SourceProduct.forward ∘ UCD.forward

    target-isEquiv : IsEquiv targetComparison
    target-isEquiv = equiv-compose TargetProduct.forward (productMap UC.forward UD.forward)
      TargetProduct.forward-isEquiv
      (productMap-isEquiv UC.forward UD.forward UC.forward-isEquiv UD.forward-isEquiv)

    source-isEquiv : IsEquiv sourceComparison
    source-isEquiv = equiv-compose UCD.forward SourceProduct.forward
      UCD.forward-isEquiv SourceProduct.forward-isEquiv

    comparison-square : (targetComparison ∘ mapPost forward) =₁ sourceComparison
    comparison-square =
      (pair-pre (mapPost pr₁) (mapPost pr₂) UCD.forward) ⁻¹ ∙
      (pair-cong (postcomposition T pr₁) (postcomposition T pr₂) ∙
      (pair-after UC.forward UD.forward (mapPost (funPost pr₁)) (mapPost (funPost pr₂)) ∙
      ((productMap UC.forward UD.forward ◁ mapPost-pair (funPost pr₁) (funPost pr₂)) ∙
        comp-assoc (mapPost forward) TargetProduct.forward (productMap UC.forward UD.forward))))

    comparison-isEquiv : IsEquiv (mapPost {C = T} forward)
    comparison-isEquiv = equiv-cancel-left (mapPost forward) targetComparison target-isEquiv
      (equiv-transport (comparison-square ⁻¹) source-isEquiv)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = post-tests-all forward OnMaps.comparison-isEquiv
```
