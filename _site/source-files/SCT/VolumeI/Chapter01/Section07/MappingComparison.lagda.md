# Mapping animae inside functor categories

For `prop:Mapping_Anima_Comparison`, factor the canonical inclusion through
the core using the preceding comparison, including its compatibility with
inclusions. Postcomposition with this equivalence and then the core
inclusion is an equivalence for every anima parameter.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.MappingComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M F public
  using (mappingInclusion)
import SCT.VolumeI.Chapter01.Section07.CoreOfFun as CoreComparison
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M

module InclusionComparison (X C D : CAT) (xAn : isAn X) where
  module K = CoreComparison.CoreOfFun 𝒯 M F C D
  inclusion = mappingInclusion C D

  inclusion-on-maps :
    (mapPost (coreInclusion (Fun C D)) ∘ mapPost {C = X} K.comparison) =₁
    (mapPost inclusion)
  inclusion-on-maps = mapPost-cong K.inclusion-comparison ∙
    mapPost-comp K.comparison (coreInclusion (Fun C D))

  inclusion-isEquiv : IsEquiv (mapPost {C = X} inclusion)
  inclusion-isEquiv = equiv-transport inclusion-on-maps
    (equiv-compose (mapPost K.comparison) (mapPost (coreInclusion (Fun C D)))
      (mapPost-isEquiv K.comparison K.comparison-isEquiv)
      (core-universal X (Fun C D) xAn))
```
