# Extending cocones through a pushout

The defining mapping-anima pullback extends every ordinary compatible
cocone. It also reflects comparisons between extensions. Naming and
decoding retain the specified matching in both constructions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section08.DecodeRestrictionCones as Decode
import SCT.VolumeI.Chapter01.Section08.DecodeSquareEvaluation as Evaluation

module SCT.VolumeI.Chapter01.Section08.PushoutExtensions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.SquareCocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeUniversality 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (coconePost; cocone-action)
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P
module DC = Decode 𝒯 M

module Extensions {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) (universal : IsPushout s) (E : CAT) where
  module U = UniversalCone (mappingOut s E) (universal E)
  ordinary = squareCocone s
  evaluate : (h : Obj-abs (Map D E)) →
    CoconeIso (DC.decodeRestriction {u = u} {v = l} (conePre h (mappingOut s E)))
      (coconePost (decodeMap h) ordinary)
  evaluate = Evaluation.Evaluation.comparison 𝒯 M P s

  module Lift (t : Cocone u l E) where
    module Named = DC.NameRestriction t
    name = U.factor Named.value
    value = decodeMap name

    abstract
      comparison : CoconeIso (coconePost value ordinary) t
      comparison = coconeIso-compose Named.comparison
        (coconeIso-compose (DC.decodeRestrictionIso {u = u} {v = l} (U.factor-β Named.value))
          (coconeIso-inverse (evaluate name)))

  module Compare (f g : MAP D E)
    (Φ : CoconeIso (coconePost f ordinary) (coconePost g ordinary)) where
    f′ = nameMap f
    g′ = nameMap g

    abstract
      named-comparison : ConeIso (conePre f′ (mappingOut s E)) (conePre g′ (mappingOut s E))
      named-comparison = DC.ReflectDecodedRestriction.comparison
        (conePre f′ (mappingOut s E)) (conePre g′ (mappingOut s E))
        (coconeIso-compose (coconeIso-inverse (evaluate g′))
        (coconeIso-compose (coconeIso-inverse (cocone-action ordinary (decode-name g)))
        (coconeIso-compose Φ
        (coconeIso-compose (cocone-action ordinary (decode-name f)) (evaluate f′)))))

      comparison : =₁ f g
      comparison = decode-name g ∙
        (decodeMapIso (U.reflect f′ g′ named-comparison) ∙ invIso (decode-name f))

pushout-extension-property : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) → IsPushout s → CoconeExtensionProperty (squareCocone s)
pushout-extension-property s universal = record
  { factor = Extensions.Lift.value s universal
  ; factor-β = Extensions.Lift.comparison s universal
  ; reflect = Extensions.Compare.comparison s universal }
```
