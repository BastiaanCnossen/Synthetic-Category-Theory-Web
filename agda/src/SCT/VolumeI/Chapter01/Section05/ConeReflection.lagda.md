# Reflecting cone comparisons through uncurrying

For an anima of parameters, both leg comparisons lift through uncurrying.
Endpoint transport and naturality identify the uncurried compatibility
equation, which is then reflected by the mapping axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup

module SCT.VolumeI.Chapter01.Section05.ConeReflection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section05.ConeUncurrying 𝒯 M
open import SCT.VolumeI.Chapter01.Section05.ConeCalculus 𝒯 using (coneIso-adjust)
open import SCT.VolumeI.Chapter01.Section05.MappingCompatibility 𝒯 M

module ReflectCone {X T C D E : CAT} {f : MAP C E} {g : MAP D E}
  (xAn : isAn X) (s t : Cone (mapPost {C = T} f) (mapPost g) X)
  (Φ : ConeIso (uncurryCone s) (uncurryCone t)) where

  left = mapReflect xAn _ _ (ConeIso.leftIso Φ)
  right = mapReflect xAn _ _ (ConeIso.rightIso Φ)
  adjusted = coneIso-adjust Φ (mapUncurryIso left) (mapUncurryIso right)
    (invIso (mapReflect-β xAn _ _ (ConeIso.leftIso Φ)))
    (invIso (mapReflect-β xAn _ _ (ConeIso.rightIso Φ)))
  fs = mapPost-uncurry f (Cone.left s)
  ft = mapPost-uncurry f (Cone.left t)
  gs = mapPost-uncurry g (Cone.right s)
  gt = mapPost-uncurry g (Cone.right t)
  τs = mapUncurryIso (Cone.match s)
  τt = mapUncurryIso (Cone.match t)
  α = mapUncurryIso (mapPost f ◁ left)
  β = mapUncurryIso (mapPost g ◁ right)

  rawSquare : Iso₂ (τt ∙ α) (β ∙ τs)
  rawSquare = changeEndpoints-reflect fs gt _ _
    (changeEndpoints-comp fs gs gt β τs ∙
    (isoComp-cong
      (invIso (square-to-changeEndpoints gs gt β (g ◁ mapUncurryIso right) (mapPost-uncurry-natural g right)))
      (idIso (Cone.match (uncurryCone s))) ∙
    (ConeIso.compatible adjusted ∙
    (isoComp-cong (idIso (Cone.match (uncurryCone t)))
      (square-to-changeEndpoints fs ft α (f ◁ mapUncurryIso left) (mapPost-uncurry-natural f left)) ∙
      invIso (changeEndpoints-comp fs ft gt τt α)))))

  comparison : ConeIso s t
  comparison = record
    { leftIso = left ; rightIso = right
    ; compatible = mapReflect-Iso₂ xAn _ _
        (invIso (mapUncurryIso-comp (mapPost g ◁ right) (Cone.match s)) ∙
          (rawSquare ∙ mapUncurryIso-comp (Cone.match t) (mapPost f ◁ left))) }
```
