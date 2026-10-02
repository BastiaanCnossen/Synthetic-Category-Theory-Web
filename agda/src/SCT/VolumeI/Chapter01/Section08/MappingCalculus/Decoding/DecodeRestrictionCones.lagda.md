# Decoding absolute restriction cones

Decoding an absolute cone of precomposition functors gives a compatible
cocone on the original span. Its matching and the compatibility of each
cone comparison are transported by the decoding comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodeRestrictionCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodingCalculus 𝒯 M

open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

decodeRestriction : {A B C E : CAT} {u : MAP A B} {v : MAP A C} →
  Cone (mapPre {D = E} u) (mapPre v) One →
  Cocone u v E
decodeRestriction {u = u} {v} s = record
  { left = decodeMap (Cone.left s) ; right = decodeMap (Cone.right s)
  ; match = decodePre v (Cone.right s) ∙
      (decodeMapIso (Cone.match s) ∙ (decodePre u (Cone.left s)) ⁻¹) }

decodeRestrictionIso : {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  {s t : Cone (mapPre {D = E} u) (mapPre v) One} → ConeIso s t →
  CoconeIso (decodeRestriction {u = u} {v = v} s) (decodeRestriction t)
decodeRestrictionIso {u = u} {v} {s} {t} Φ = record
  { leftIso = decodeMapIso α ; rightIso = decodeMapIso β
  ; compatible = paste-squares (τs ∙ fs ⁻¹) (τt ∙ ft ⁻¹) gs gt first third last
      (paste-squares (fs ⁻¹) (ft ⁻¹) τs τt first second third
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
      (decodeMapIso-comp (Cone.match t) (mapPre u ◁ α)) ⁻¹)
```

Naming the two legs lifts their matching through the actual decoding
equivalence. The beta comparison below is a comparison of whole cocones.

```agda
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.BoundaryTransport
  vocabulary terminal products productLaws composition vertical using (restore-boundaries)
open import SCT.VolumeI.Chapter01.Section04.Substitution.TransportedSquares 𝒯
  using (reflect-transported-square)

module NameRestriction {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v E) where

  left = nameMap (Cocone.left s)
  right = nameMap (Cocone.right s)
  left-β = decode-name (Cocone.left s)
  right-β = decode-name (Cocone.right s)
  wanted = coconeRetarget s (decodeMap left) (decodeMap right) (left-β ⁻¹) (right-β ⁻¹)
  desired = Cocone.match wanted
  leftChange = decodePre u left
  rightChange = decodePre v right
  rawMatch = rightChange ⁻¹ ∙ (desired ∙ leftChange)

  value : Cone (mapPre {D = E} u) (mapPre v) One
  value = record { left = left ; right = right ; match = decodeMap-reflect _ _ rawMatch }

  abstract
    match-β : (Cocone.match (decodeRestriction {u = u} {v = v} value)) =₂ desired
    match-β = restore-boundaries leftChange rightChange desired
      (decodeMapIso (Cone.match value))
      (decodeMap-reflect-β _ _ rawMatch)

    comparison : CoconeIso (decodeRestriction {u = u} {v = v} value) s
    comparison = coconeIso-compose
      (coconeIso-inverse (coconeRetarget-β s _ _ (left-β ⁻¹) (right-β ⁻¹)))
      (cocone-match-change _ _ _ _ match-β)

module ReflectDecodedRestriction {A B C E : CAT} {u : MAP A B} {v : MAP A C}
  (s t : Cone (mapPre {D = E} u) (mapPre v) One)
  (Φ : CoconeIso (decodeRestriction {u = u} {v = v} s) (decodeRestriction t)) where

  left = decodeMap-reflect _ _ (CoconeIso.leftIso Φ)
  right = decodeMap-reflect _ _ (CoconeIso.rightIso Φ)
  adjusted = coconeIso-adjust Φ (decodeMapIso left) (decodeMapIso right)
    ((decodeMap-reflect-β _ _ (CoconeIso.leftIso Φ)) ⁻¹)
    ((decodeMap-reflect-β _ _ (CoconeIso.rightIso Φ)) ⁻¹)
  fs = decodePre u (Cone.left s)
  ft = decodePre u (Cone.left t)
  gs = decodePre v (Cone.right s)
  gt = decodePre v (Cone.right t)
  τs = decodeMapIso (Cone.match s)
  τt = decodeMapIso (Cone.match t)
  α = decodeMapIso (mapPre u ◁ left)
  β = decodeMapIso (mapPre v ◁ right)

  abstract
    rawSquare : (τt ∙ α) =₂ (β ∙ τs)
    rawSquare = reflect-transported-square fs gs ft gt τs τt
      α β (decodeMapIso left ▷ u) (decodeMapIso right ▷ v)
      (decodePre-absolute u left) (decodePre-absolute v right)
      (CoconeIso.compatible adjusted)

    comparison : ConeIso s t
    comparison = record
      { leftIso = left ; rightIso = right
      ; compatible = decodeMap-reflect-Iso₂ _ _
          ((decodeMapIso-comp (mapPre v ◁ right) (Cone.match s)) ⁻¹ ∙
            (rawSquare ∙ decodeMapIso-comp (Cone.match t) (mapPre u ◁ left))) }

    left-image : (decodeMapIso (ConeIso.leftIso comparison)) =₂ (CoconeIso.leftIso Φ)
    left-image = decodeMap-reflect-β _ _ (CoconeIso.leftIso Φ)

    right-image : (decodeMapIso (ConeIso.rightIso comparison)) =₂ (CoconeIso.rightIso Φ)
    right-image = decodeMap-reflect-β _ _ (CoconeIso.rightIso Φ)
```
