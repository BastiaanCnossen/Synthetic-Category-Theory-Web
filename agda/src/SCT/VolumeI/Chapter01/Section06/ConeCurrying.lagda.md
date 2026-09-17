# Currying a cone

Currying the two legs also curries the matching, with its specified
uncurrying comparison. The resulting cone comparison retains the
compatibility of those three choices.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.ConeCurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeUncurrying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.ConeCalculus 𝒯 using (coneRetarget; coneRetarget-β; coneIso-compose; coneIso-inverse)
open import SCT.VolumeI.Chapter01.Section05.ConeSymmetry 𝒯 using (cone-match-change)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module CurryCone {X T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g (X × T)) where

  left = funCurry (Cone.left s)
  right = funCurry (Cone.right s)
  left-β = funCurry-β (Cone.left s)
  right-β = funCurry-β (Cone.right s)
  wanted = coneRetarget s (funUncurry left) (funUncurry right) (invIso left-β) (invIso right-β)
  desired = Cone.match wanted
  leftChange = funPost-uncurry f left
  rightChange = funPost-uncurry g right
  rawMatch = invIso rightChange ∙ (desired ∙ leftChange)

  value : Cone (funPost f) (funPost g) X
  value = record
    { left = left ; right = right
    ; match = funIsoReflect _ _ rawMatch }

  match-β : =₂ (Cone.match (uncurryCone value)) desired
  match-β = cancel-right leftChange desired ∙
    (isoComp-cong (cancel-inverse rightChange (desired ∙ leftChange)) (idIso (invIso leftChange)) ∙
    (invIso (isoComp-assoc-at rightChange rawMatch (invIso leftChange)) ∙
      isoComp-cong (idIso rightChange)
        (isoComp-cong (funIsoReflect-β _ _ rawMatch) (idIso (invIso leftChange)))))

  abstract
    comparison : ConeIso (uncurryCone value) s
    comparison = coneIso-compose
      (coneIso-inverse (coneRetarget-β s _ _ (invIso left-β) (invIso right-β)))
      (cone-match-change _ _ _ _ match-β)
```

