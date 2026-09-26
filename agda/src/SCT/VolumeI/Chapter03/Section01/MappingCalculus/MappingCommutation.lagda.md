# Precomposition commutes with postcomposition

The comparison follows by uncurrying and associating composition.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M

mapPre-mapPost : {A B C D : CAT} (f : MAP A B) (g : MAP C D) →
  (mapPre f ∘ mapPost g) =₁ (mapPost g ∘ mapPre f)
mapPre-mapPost {B = B} {C} f g = mapReflect (map-isAn B C) _ _
  ((mapPost-uncurry g (mapPre f)) ⁻¹ ∙
    ((g ◁ mapPre-β f) ⁻¹ ∙
      (comp-assoc (productMap (id (Map B C)) f) mapEval g ∙
        ((mapPost-β g ▷ productMap (id (Map B C)) f) ∙ mapPre-uncurry f (mapPost g)))))

```
