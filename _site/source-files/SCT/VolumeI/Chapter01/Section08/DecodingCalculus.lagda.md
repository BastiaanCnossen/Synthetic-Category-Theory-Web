# Decoding comparisons of restrictions

These two computations specialize the existing decoding naturality and
composition rules to absolute isomorphisms. They retain the actual
decoding functor on each isomorphism anima.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section08.DecodingCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.DecodingNaturality 𝒯 M public using (decodePre)
import SCT.VolumeI.Chapter01.Section04.DecodingNaturality as DN

decodePre-absolute : {B C E : CAT} (i : MAP B C)
  {u v : Obj-abs (Map C E)} (γ : u =₁ v) →
  (decodePre i v ∙ decodeMapIso (mapPre i ◁ γ)) =₂
    ((decodeMapIso γ ▷ i) ∙ decodePre i u)
decodePre-absolute i {u} {v} γ =
  isoComp-cong (idIso (decodeMapIso γ ▷ i)) (const-One (decodePre i u)) ∙
  (DN.decodePre-natural 𝒯 M i γ ∙
    (isoComp-cong (const-One (decodePre i v)) (idIso (decodeMapIso (mapPre i ◁ γ)))) ⁻¹)

decodeMapIso-comp : {C E : CAT} {u v w : Obj-abs (Map C E)}
  (β : v =₁ w) (α : u =₁ v) →
  (decodeMapIso (β ∙ α)) =₂ (decodeMapIso β ∙ decodeMapIso α)
decodeMapIso-comp {C} β α =
  isoComp-cong ((decodeMapIso-at β) ⁻¹) ((decodeMapIso-at α) ⁻¹) ∙
  (preWhisker-isoComp-at (mapUncurryIso β) (mapUncurryIso α) (oneProduct-in C) ∙
  ((preWhisker (oneProduct-in C) ◁ mapUncurryIso-comp β α) ∙ decodeMapIso-at (β ∙ α)))
```
