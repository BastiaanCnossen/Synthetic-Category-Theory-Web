# Currying a cone

Currying the two legs also curries the matching, with its specified
uncurrying comparison. The resulting cone comparison retains the
compatibility of those three choices.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section06.ConeCurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.ConeUncurrying 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus 𝒯 using (coneRetarget; coneRetarget-β; coneIso-compose; coneIso-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (cone-match-change)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module CurryCone {X T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (xAn : isAn X) (s : Cone f g (X × T)) where

  left = mapCurry xAn (Cone.left s)
  right = mapCurry xAn (Cone.right s)
  left-β = mapCurry-β xAn (Cone.left s)
  right-β = mapCurry-β xAn (Cone.right s)
  wanted = coneRetarget s (mapUncurry left) (mapUncurry right) (left-β ⁻¹) (right-β ⁻¹)
  desired = Cone.match wanted
  leftChange = mapPost-uncurry f left
  rightChange = mapPost-uncurry g right
  rawMatch = rightChange ⁻¹ ∙ (desired ∙ leftChange)

  value : Cone (mapPost f) (mapPost g) X
  value = record
    { left = left ; right = right
    ; match = mapReflect xAn _ _ rawMatch }

  match-β : (Cone.match (uncurryCone value)) =₂ desired
  match-β = cancel-right leftChange desired ∙
    (isoComp-cong (cancel-inverse rightChange (desired ∙ leftChange)) (idIso (leftChange ⁻¹)) ∙
    ((isoComp-assoc-at rightChange rawMatch (leftChange ⁻¹)) ⁻¹ ∙
      isoComp-cong (idIso rightChange)
        (isoComp-cong (mapReflect-β xAn _ _ rawMatch) (idIso (leftChange ⁻¹)))))

  abstract
    comparison : ConeIso (uncurryCone value) s
    comparison = coneIso-compose
      (coneIso-inverse (coneRetarget-β s _ _ (left-β ⁻¹) (right-β ⁻¹)))
      (cone-match-change _ _ _ _ match-β)
```
