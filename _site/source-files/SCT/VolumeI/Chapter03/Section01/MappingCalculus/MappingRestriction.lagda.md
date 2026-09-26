# Restricting the test category in the mapping action

Acting on maps and then restricting their source agrees with restricting
first. We use this comparison at the two endpoints of `[1]` when proving
the universal property of a full subcategory.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Composition 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence 𝒯 M using (compose-assoc)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M

mapPre-compose : {Γ A B C D : CAT} (f : MAP A B)
  (g : MAP Γ (Map C D)) (h : MAP Γ (Map B C)) → isAn Γ →
  (mapPre f ∘ composeTerm g h) =₁ composeTerm g (mapPre f ∘ h)
mapPre-compose f g h Γ-an = composeTerm-cong (idIso g) (compose-named-right f h Γ-an) ∙
  (compose-assoc Γ-an g h (const (nameMap f)) ∙
    (compose-named-right f (composeTerm g h) Γ-an) ⁻¹)

mapComp-pre : {A B C D : CAT} (f : MAP A B) →
  (mapPre f ∘ mapComp {B} {C} {D}) =₁
    (mapComp ∘ productMap (id (Map C D)) (mapPre f))
mapComp-pre {B = B} {C} {D} f =
  (mapComp ◁ pair-cong (comp-unitˡ pr₁) (idIso (mapPre f ∘ pr₂))) ⁻¹ ∙
    (mapPre-compose f pr₁ pr₂ (product-isAn (map-isAn C D) (map-isAn B C)) ∙
      (mapPre f ◁ mapComp-projections ⁻¹))

mappingAction-restrict : {A B : CAT} (f : MAP A B) (C D : CAT) →
  (mapPost (mapPre {D = D} f) ∘ mappingAction B C D) =₁
    (mapPre (mapPre {D = C} f) ∘ mappingAction A C D)
mappingAction-restrict {A} {B} f C D = mapReflect (map-isAn C D) _ _
  (right ⁻¹ ∙ (mapComp-pre f ∙ left))
  where
  left = (mapPre f ◁ mappingAction-β B C D) ∙
    mapPost-uncurry (mapPre f) (mappingAction B C D)
  right = (mappingAction-β A C D ▷ productMap (id (Map C D)) (mapPre f)) ∙
    mapPre-uncurry (mapPre f) (mappingAction A C D)
```
