# Decoding absolute restriction cones

Decoding an absolute cone of precomposition functors gives a compatible
cocone on the original span. Its matching and the compatibility of each
cone comparison are transported by the decoding comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping

import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.DecodeRestrictionCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.DecodingCalculus 𝒯 M

open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

decodeRestriction : {A B C E : CAT} {u : MAP A B} {v : MAP A C} →
  Cone (mapPre {D = E} u) (mapPre v) One →
  Cocone u v E
decodeRestriction {u = u} {v} s = record
  { left = decodeMap (Cone.left s) ; right = decodeMap (Cone.right s)
  ; match = decodePre v (Cone.right s) ∙
      (decodeMapIso (Cone.match s) ∙ invIso (decodePre u (Cone.left s))) }

decodeRestrictionIso : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  {s t : Cone (mapPre {D = E} u) (mapPre v) One} → ConeIso s t →
  CoconeIso (decodeRestriction {u = u} {v = v} s) (decodeRestriction t)
decodeRestrictionIso {u = u} {v} {s} {t} Φ = record
  { leftIso = decodeMapIso α ; rightIso = decodeMapIso β
  ; compatible = paste-squares (τs ∙ invIso fs) (τt ∙ invIso ft) gs gt first third last
      (paste-squares (invIso fs) (invIso ft) τs τt first second third
        (move-square ft second first fs (decodePre-absolute u α)) rawSquare)
      (decodePre-absolute v β) }
  where
  α = ConeIso.leftIso Φ
  β = ConeIso.rightIso Φ
  fs = decodePre u (Cone.left s)
  ft = decodePre u (Cone.left t)
  gs = decodePre v (Cone.right s)
  gt = decodePre v (Cone.right t)
  τs = decodeMapIso (Cone.match s)
  τt = decodeMapIso (Cone.match t)
  first = decodeMapIso α ▷ u
  second = decodeMapIso (mapPre u ◁ α)
  third = decodeMapIso (mapPre v ◁ β)
  last = decodeMapIso β ▷ v
  rawSquare = decodeMapIso-comp (mapPre v ◁ β) (Cone.match s) ∙
    ((decodeMap-isoMap _ _ ◁ ConeIso.compatible Φ) ∙
      invIso (decodeMapIso-comp (Cone.match t) (mapPre u ◁ α)))
```

Naming the two legs lifts their matching through the actual decoding
equivalence. The beta comparison below is a comparison of whole cocones.

```agda
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open import SCT.VolumeI.Chapter01.Section01.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯

module NameRestriction {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v E) where

  left = nameMap (Cocone.left s)
  right = nameMap (Cocone.right s)
  left-β = decode-name (Cocone.left s)
  right-β = decode-name (Cocone.right s)
  wanted = coconeRetarget s (decodeMap left) (decodeMap right) (invIso left-β) (invIso right-β)
  desired = Cocone.match wanted
  leftChange = decodePre u left
  rightChange = decodePre v right
  rawMatch = invIso rightChange ∙ (desired ∙ leftChange)

  value : Cone (mapPre {D = E} u) (mapPre v) One
  value = record { left = left ; right = right ; match = decodeMap-reflect _ _ rawMatch }

  abstract
    match-β : =₂ (Cocone.match (decodeRestriction {u = u} {v = v} value)) desired
    match-β = cancel-right leftChange desired ∙
      (isoComp-cong (cancel-inverse rightChange (desired ∙ leftChange)) (idIso (invIso leftChange)) ∙
      (invIso (isoComp-assoc-at rightChange rawMatch (invIso leftChange)) ∙
        isoComp-cong (idIso rightChange)
          (isoComp-cong (decodeMap-reflect-β _ _ rawMatch) (idIso (invIso leftChange)))))

    comparison : CoconeIso (decodeRestriction {u = u} {v = v} value) s
    comparison = coconeIso-compose
      (coconeIso-inverse (coconeRetarget-β s _ _ (invIso left-β) (invIso right-β)))
      (cocone-match-change _ _ _ _ match-β)

module ReflectDecodedRestriction {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s t : Cone (mapPre {D = E} u) (mapPre v) One)
  (Φ : CoconeIso (decodeRestriction {u = u} {v = v} s) (decodeRestriction t)) where

  left = decodeMap-reflect _ _ (CoconeIso.leftIso Φ)
  right = decodeMap-reflect _ _ (CoconeIso.rightIso Φ)
  adjusted = coconeIso-adjust Φ (decodeMapIso left) (decodeMapIso right)
    (invIso (decodeMap-reflect-β _ _ (CoconeIso.leftIso Φ)))
    (invIso (decodeMap-reflect-β _ _ (CoconeIso.rightIso Φ)))
  fs = decodePre u (Cone.left s)
  ft = decodePre u (Cone.left t)
  gs = decodePre v (Cone.right s)
  gt = decodePre v (Cone.right t)
  τs = decodeMapIso (Cone.match s)
  τt = decodeMapIso (Cone.match t)
  α = decodeMapIso (mapPre u ◁ left)
  β = decodeMapIso (mapPre v ◁ right)

  abstract
    rawSquare : =₂ (τt ∙ α) (β ∙ τs)
    rawSquare = changeEndpoints-reflect fs gt _ _
      (changeEndpoints-comp fs gs gt β τs ∙
      (isoComp-cong
        (invIso (square-to-changeEndpoints gs gt β
          (decodeMapIso right ▷ v) (decodePre-absolute v right)))
        (idIso (Cocone.match (decodeRestriction s))) ∙
      (CoconeIso.compatible adjusted ∙
      (isoComp-cong (idIso (Cocone.match (decodeRestriction t)))
        (square-to-changeEndpoints fs ft α
          (decodeMapIso left ▷ u) (decodePre-absolute u left)) ∙
        invIso (changeEndpoints-comp fs ft gt τt α)))))

    comparison : ConeIso s t
    comparison = record
      { leftIso = left ; rightIso = right
      ; compatible = decodeMap-reflect-Iso₂ _ _
          (invIso (decodeMapIso-comp (mapPre v ◁ right) (Cone.match s)) ∙
            (rawSquare ∙ decodeMapIso-comp (Cone.match t) (mapPre u ◁ left))) }

    left-image : =₂ (decodeMapIso (ConeIso.leftIso comparison)) (CoconeIso.leftIso Φ)
    left-image = decodeMap-reflect-β _ _ (CoconeIso.leftIso Φ)

    right-image : =₂ (decodeMapIso (ConeIso.rightIso comparison)) (CoconeIso.rightIso Φ)
    right-image = decodeMap-reflect-β _ _ (CoconeIso.rightIso Φ)
```
