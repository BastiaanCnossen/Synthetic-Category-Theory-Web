# The core of a functor category

For `core_of_Fun_is_Map`, lift the mapping-anima inclusion to the core,
retaining its comparison with the inclusion. Testing on animae identifies
its postcomposition functor by cancellation between the two universal
properties. Equivalence detection then proves the preferred map is an
equivalence. No assertion that every category is an anima is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.CoreOfFun
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section07.MappingComparison 𝒯 M F
open import SCT.VolumeI.Chapter01.Section07.Core 𝒯 M F
open import SCT.VolumeI.Chapter01.Section03.EquivalenceDetection 𝒯 M using (post-tests-animae)

module CoreOfFun (C D : CAT) where
  module Lift = CoreLift (map-isAn C D) (mappingInclusion C D)
  comparison : MAP (Map C D) (Core (Fun C D))
  comparison = Lift.lift

  inclusion-comparison : =₁ (coreInclusion (Fun C D) ∘ comparison) (mappingInclusion C D)
  inclusion-comparison = Lift.comparison

  comparison-on-maps : (X : CAT) → isAn X → IsEquiv (mapPost {C = X} comparison)
  comparison-on-maps X xAn = equiv-cancel-left (mapPost comparison) (mapPost (coreInclusion (Fun C D)))
    (core-universal X (Fun C D) xAn)
    (equiv-transport (invIso (mapPost-cong inclusion-comparison ∙ mapPost-comp comparison (coreInclusion (Fun C D))))
      (InclusionComparison.inclusion-isEquiv X C D xAn))

  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = post-tests-animae (map-isAn C D) (core-isAn (Fun C D)) comparison comparison-on-maps
```

