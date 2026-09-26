# Postcomposition by an equivalence over the base

The native inverse and its two triangle-compatible inverse laws induce
inverse functors on relative functor categories. The same conclusion
holds for the specified postcomposition map on relative mapping animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Equivalences 𝒯 M ℱ P using (module Inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionLaws 𝒯 M ℱ P

module Post {A C D S : CAT} (r : MAP A S) {f : MAP C S} {g : MAP D S}
  (u : FunctorOver f g) (equivalence : IsEquiv (FunctorLift.lift u)) where
  module Inverted = Inverse u equivalence
  module Forward = Postcompose r u
  module Backward = Postcompose r Inverted.inverse

  abstract
    functor-isEquiv : IsEquiv Forward.functor
    functor-isEquiv = record
      { inverse = Backward.functor
      ; sectionIso = (postcompose-identity r f ∙
          (postcompose-identification r Inverted.left-inverse ∙ postcompose-composite r u Inverted.inverse)) ⁻¹
      ; retractionIso = (postcompose-identity r g ∙
          (postcompose-identification r Inverted.right-inverse ∙ postcompose-composite r Inverted.inverse u)) ⁻¹ }

    maps-isEquiv : IsEquiv Forward.maps
    maps-isEquiv = equiv-transport (Forward.maps-as-core ⁻¹) (mapPost-isEquiv Forward.functor functor-isEquiv)
```
