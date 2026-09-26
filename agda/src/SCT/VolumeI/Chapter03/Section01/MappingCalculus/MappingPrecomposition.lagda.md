# Precomposing a functor before acting on maps

Composition of the internal mapping terms gives naturality in the
source category. This is the comparison used when restricting functors
that invert a collection.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingPrecomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Composition 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence 𝒯 M using (compose-assoc)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M

compose-precompose : {Γ E C D F : CAT} (f : MAP C D)
  (g : MAP Γ (Map D F)) (h : MAP Γ (Map E C)) → isAn Γ →
  composeTerm (mapPre f ∘ g) h =₁ composeTerm g (mapPost f ∘ h)
compose-precompose f g h Γ-an = composeTerm-cong (idIso g) (compose-nameMap f h Γ-an) ∙
  (compose-assoc Γ-an g (const (nameMap f)) h ∙
    composeTerm-cong ((compose-named-right f g Γ-an) ⁻¹) (idIso h))

mapComp-precompose : {C D : CAT} (f : MAP C D) (E F : CAT) →
  (mapComp ∘ productMap (mapPre {D = F} f) (id (Map E C))) =₁
    (mapComp ∘ productMap (id (Map D F)) (mapPost {C = E} f))
mapComp-precompose {C} {D} f E F =
  (mapComp ◁ pair-cong (comp-unitˡ pr₁) (idIso (mapPost f ∘ pr₂))) ⁻¹ ∙
    (compose-precompose f pr₁ pr₂ (product-isAn (map-isAn D F) (map-isAn E C)) ∙
      (mapComp ◁ pair-cong (idIso (mapPre f ∘ pr₁)) (comp-unitˡ pr₂)))

mappingAction-precompose : {C D : CAT} (f : MAP C D) (E F : CAT) →
  (mappingAction E C F ∘ mapPre f) =₁
    (mapPre (mapPost {C = E} f) ∘ mappingAction E D F)
mappingAction-precompose {C} {D} f E F = mapReflect (map-isAn D F) _ _
  (right ⁻¹ ∙ (mapComp-precompose f E F ∙ left))
  where
  left = (mappingAction-β E C F ▷ productMap (mapPre f) (id (Map E C))) ∙
    mapUncurry-restrict (mappingAction E C F) (mapPre f)
  right = (mappingAction-β E D F ▷ productMap (id (Map D F)) (mapPost f)) ∙
    mapPre-uncurry (mapPost f) (mappingAction E D F)
```
