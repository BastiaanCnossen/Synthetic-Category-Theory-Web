# Prescribed comparisons between pushout extensions

A comparison of the two restricted cocones lifts to a comparison of the
extensions. Both restrictions of this lift agree with the prescribed
legs. These identifications are needed when cancelling a pushout square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section08.DecodeRestrictionCones as Decode
import SCT.VolumeI.Chapter01.Section08.DecodeSquareEvaluation as Evaluation
import SCT.VolumeI.Chapter01.Section05.UniversalConeLifting as Lifting

module SCT.VolumeI.Chapter01.Section08.PushoutComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.SquareCocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeUniversality 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (coconePost; cocone-action)
open import SCT.VolumeI.Chapter01.Section08.DecodingCalculus 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.DecodedLegCalculus 𝒯
module DC = Decode 𝒯 M

module PrescribedComparison {A B C D E : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) (universal : IsPushout s)
  (f g : MAP D E)
  (Φ : CoconeIso (coconePost f (squareCocone s)) (coconePost g (squareCocone s))) where

  ordinary : Cocone u l D
  ordinary = squareCocone s
  f′ : ObjAbs (Map D E)
  f′ = nameMap f
  g′ : ObjAbs (Map D E)
  g′ = nameMap g
  evaluate : (h : ObjAbs (Map D E)) →
    CoconeIso (DC.decodeRestriction {u = u} {v = l} (conePre h (mappingOut s E)))
      (coconePost (decodeMap h) ordinary)
  evaluate = Evaluation.Evaluation.comparison 𝒯 M P s

  decoded-comparison : CoconeIso
    (DC.decodeRestriction {u = u} {v = l} (conePre f′ (mappingOut s E)))
    (DC.decodeRestriction (conePre g′ (mappingOut s E)))
  decoded-comparison = coconeIso-compose (coconeIso-inverse (evaluate g′))
    (coconeIso-compose (coconeIso-inverse (cocone-action ordinary (decode-name g)))
    (coconeIso-compose Φ
    (coconeIso-compose (cocone-action ordinary (decode-name f)) (evaluate f′))))

  module Encoded = DC.ReflectDecodedRestriction
    (conePre f′ (mappingOut s E)) (conePre g′ (mappingOut s E)) decoded-comparison
  module Lift = Lifting.UniversalLift 𝒯 P (mappingOut s E) (universal E)
    f′ g′ Encoded.comparison

  decoded-lift : NatIso (decodeMap f′) (decodeMap g′)
  decoded-lift = decodeMapIso Lift.lift
  lift : NatIso f g
  lift = decode-name g ∙ (decoded-lift ∙ invIso (decode-name f))

  abstract
    leg-image : {T : CAT} (j : MAP T D) (γ : NatIso (f ∘ j) (g ∘ j)) →
      Iso₂ (decodeMapIso (mapPre j ◁ Lift.lift))
        (invIso (decodePre j g′) ∙
          (invIso (decode-name g ▷ j) ∙
            (γ ∙ ((decode-name f ▷ j) ∙ decodePre j f′)))) →
      Iso₂ (lift ▷ j) γ
    leg-image j γ prescribed =
      decoded-leg (decodePre j f′) (decodePre j g′)
        (decode-name f ▷ j) (decode-name g ▷ j) γ
        (decodeMapIso (mapPre j ◁ Lift.lift)) (decoded-lift ▷ j)
        (decodePre-absolute j Lift.lift) prescribed ∙ normal
      where
      normal : Iso₂ (lift ▷ j)
        (changeEndpoints (decode-name f ▷ j) (decode-name g ▷ j) (decoded-lift ▷ j))
      normal = isoComp-cong (idIso (decode-name g ▷ j))
        (isoComp-cong (idIso (decoded-lift ▷ j)) (pre-inverse (decode-name f) j) ∙
          preWhisker-isoComp-at decoded-lift (invIso (decode-name f)) j) ∙
        preWhisker-isoComp-at (decode-name g) (decoded-lift ∙ invIso (decode-name f)) j

    left-image : Iso₂ (lift ▷ r) (CoconeIso.leftIso Φ)
    left-image = leg-image r (CoconeIso.leftIso Φ)
      (Encoded.left-image ∙ (decodeMap-isoMap _ _ ◁ Lift.left-image))

    right-image : Iso₂ (lift ▷ v) (CoconeIso.rightIso Φ)
    right-image = leg-image v (CoconeIso.rightIso Φ)
      (Encoded.right-image ∙ (decodeMap-isoMap _ _ ◁ Lift.right-image))

  comparison : CoconeComparisonLift ordinary f g Φ
  comparison = record { lift = lift ; left-image = left-image ; right-image = right-image }
```
