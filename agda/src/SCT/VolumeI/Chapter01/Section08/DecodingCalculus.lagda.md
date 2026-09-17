# Decoding comparisons of restrictions

These two computations specialize the existing decoding naturality and
composition rules to absolute isomorphisms. They retain the actual
decoding functor on each isomorphism anima.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section08.DecodingCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.DecodingNaturality 𝒯 M public using (decodePre)
import SCT.VolumeI.Chapter01.Section03.DecodingNaturality as DN

decodePre-absolute : {B C E : CAT} (i : MAP B C)
  {u v : Obj-abs (Map C E)} (γ : =₁ u v) →
  =₂ (decodePre i v ∙ decodeMapIso (mapPre i ◁ γ))
    ((decodeMapIso γ ▷ i) ∙ decodePre i u)
decodePre-absolute i {u} {v} γ =
  isoComp-cong (idIso (decodeMapIso γ ▷ i)) (const-One (decodePre i u)) ∙
  (DN.decodePre-natural 𝒯 M i γ ∙
    invIso (isoComp-cong (const-One (decodePre i v)) (idIso (decodeMapIso (mapPre i ◁ γ)))))

decodeMapIso-comp : {C E : CAT} {u v w : Obj-abs (Map C E)}
  (β : =₁ v w) (α : =₁ u v) →
  =₂ (decodeMapIso (β ∙ α)) (decodeMapIso β ∙ decodeMapIso α)
decodeMapIso-comp {C} β α =
  isoComp-cong (invIso (decodeMapIso-at β)) (invIso (decodeMapIso-at α)) ∙
  (preWhisker-isoComp-at (mapUncurryIso β) (mapUncurryIso α) (oneProduct-in C) ∙
  ((preWhisker (oneProduct-in C) ◁ mapUncurryIso-comp β α) ∙ decodeMapIso-at (β ∙ α)))
```
