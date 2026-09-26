# Pasting higher cone comparisons

Encode a higher comparison as an ordinary comparison of cones in the
leg-identification animae. Pasting and inversion then retain the complete
matching witness. Decoding gives the higher comparison, together with
computations for both of its legs.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.HigherComparisons
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯
  using (coneIso-compose; coneIso-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeComparisonEncoding 𝒯 using (module Encoding)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.HigherReflection 𝒯 P using (module Encoded)

module Calculus {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s t : Cone f g T) where
  module E = Encoding s t
  module Higher = Encoded s t using (triangle; comparison)

  opaque
    decode-between : {Φ Ψ : ConeIso s t} → ConeIso (E.encode Φ) (E.encode Ψ) → ConeIso₂ Φ Ψ
    decode-between {Φ} {Ψ} Ω = record
      { leftId = ConeIso₂.leftId decoded ; rightId = ConeIso₂.rightId decoded
      ; compatible = isoComp-cong (idIso (ConeIso₂.rightBoundary decoded)) (Higher.triangle Φ) ∙
          ConeIso₂.compatible decoded }
      where
      decoded : ConeIso₂ (E.decode (E.encode Φ)) Ψ
      decoded = E.decode-into (E.encode Φ) Ψ Ω

  opaque
    unfolding decode-between E.decode-into E.decode-comparison
    decode-left : {Φ Ψ : ConeIso s t} (Ω : ConeIso (E.encode Φ) (E.encode Ψ)) →
      ConeIso₂.leftId (decode-between {Φ = Φ} {Ψ = Ψ} Ω) =₃ ConeIso.leftIso Ω
    decode-left Ω = idIso _

    decode-right : {Φ Ψ : ConeIso s t} (Ω : ConeIso (E.encode Φ) (E.encode Ψ)) →
      ConeIso₂.rightId (decode-between {Φ = Φ} {Ψ = Ψ} Ω) =₃ ConeIso.rightIso Ω
    decode-right Ω = idIso _

  opaque
    unfolding Higher.comparison
    encode-left : {Φ Ψ : ConeIso s t} (Ξ : ConeIso₂ Φ Ψ) →
      ConeIso.leftIso (Higher.comparison Ξ) =₃ ConeIso₂.leftId Ξ
    encode-left Ξ = idIso _

    encode-right : {Φ Ψ : ConeIso s t} (Ξ : ConeIso₂ Φ Ψ) →
      ConeIso.rightIso (Higher.comparison Ξ) =₃ ConeIso₂.rightId Ξ
    encode-right Ξ = idIso _

  opaque
    identity : (Φ : ConeIso s t) → ConeIso₂ Φ Φ
    identity Φ = decode-between {Φ = Φ} {Ψ = Φ} (coneIso-id (E.encode Φ))

    compose : {Φ Ψ Ω : ConeIso s t} → ConeIso₂ Ψ Ω → ConeIso₂ Φ Ψ → ConeIso₂ Φ Ω
    compose {Φ} {Ψ} {Ω} β α = decode-between {Φ = Φ} {Ψ = Ω}
      (coneIso-compose (Higher.comparison {Φ = Ψ} {Ψ = Ω} β) (Higher.comparison {Φ = Φ} {Ψ = Ψ} α))

    inverse : {Φ Ψ : ConeIso s t} → ConeIso₂ Φ Ψ → ConeIso₂ Ψ Φ
    inverse {Φ} {Ψ} α = decode-between {Φ = Ψ} {Ψ = Φ}
      (coneIso-inverse (Higher.comparison {Φ = Φ} {Ψ = Ψ} α))

    compose-left : {Φ Ψ Ω : ConeIso s t} (β : ConeIso₂ Ψ Ω) (α : ConeIso₂ Φ Ψ) →
      ConeIso₂.leftId (compose {Φ = Φ} {Ψ = Ψ} {Ω = Ω} β α) =₃
        (ConeIso₂.leftId β ∙ ConeIso₂.leftId α)
    compose-left {Φ} {Ψ} {Ω} β α =
      isoComp-cong (encode-left {Φ = Ψ} {Ψ = Ω} β) (encode-left {Φ = Φ} {Ψ = Ψ} α) ∙
      decode-left {Φ = Φ} {Ψ = Ω} (coneIso-compose
        (Higher.comparison {Φ = Ψ} {Ψ = Ω} β) (Higher.comparison {Φ = Φ} {Ψ = Ψ} α))

    compose-right : {Φ Ψ Ω : ConeIso s t} (β : ConeIso₂ Ψ Ω) (α : ConeIso₂ Φ Ψ) →
      ConeIso₂.rightId (compose {Φ = Φ} {Ψ = Ψ} {Ω = Ω} β α) =₃
        (ConeIso₂.rightId β ∙ ConeIso₂.rightId α)
    compose-right {Φ} {Ψ} {Ω} β α =
      isoComp-cong (encode-right {Φ = Ψ} {Ψ = Ω} β) (encode-right {Φ = Φ} {Ψ = Ψ} α) ∙
      decode-right {Φ = Φ} {Ψ = Ω} (coneIso-compose
        (Higher.comparison {Φ = Ψ} {Ψ = Ω} β) (Higher.comparison {Φ = Φ} {Ψ = Ψ} α))

    inverse-left : {Φ Ψ : ConeIso s t} (α : ConeIso₂ Φ Ψ) →
      ConeIso₂.leftId (inverse {Φ = Φ} {Ψ = Ψ} α) =₃ (ConeIso₂.leftId α) ⁻¹
    inverse-left {Φ} {Ψ} α = (＝-inv ◁ encode-left {Φ = Φ} {Ψ = Ψ} α) ∙
      decode-left {Φ = Ψ} {Ψ = Φ} (coneIso-inverse (Higher.comparison {Φ = Φ} {Ψ = Ψ} α))

    inverse-right : {Φ Ψ : ConeIso s t} (α : ConeIso₂ Φ Ψ) →
      ConeIso₂.rightId (inverse {Φ = Φ} {Ψ = Ψ} α) =₃ (ConeIso₂.rightId α) ⁻¹
    inverse-right {Φ} {Ψ} α = (＝-inv ◁ encode-right {Φ = Φ} {Ψ = Ψ} α) ∙
      decode-right {Φ = Ψ} {Ψ = Φ} (coneIso-inverse (Higher.comparison {Φ = Φ} {Ψ = Ψ} α))
```
