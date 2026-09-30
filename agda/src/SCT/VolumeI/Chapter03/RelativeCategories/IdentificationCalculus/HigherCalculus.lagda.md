# Composing full higher comparisons over a base

Encode a higher comparison as a comparison of pullback cones. Composition
and inversion of these cones retain their matching witnesses. Decoding
and normalizing the two endpoint triangles gives the corresponding
operations on full higher relative comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.HigherCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯
  using (coneIso-compose; coneIso-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonEncoding 𝒯 M ℱ P using (module Encoding)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.HigherEncoding 𝒯 M ℱ P using (module Higher)

module Calculus {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u v : FunctorOver f g) where
  module Encoded = Encoding u v
  module HigherInput = Higher u v

  opaque
    decode-between : {Φ Ψ : FunctorOverIso u v} →
      ConeIso (Encoded.encode Φ) (Encoded.encode Ψ) → FunctorOverIso₂ Φ Ψ
    decode-between {Φ} {Ψ} Ω = record
      { underlying = FunctorOverIso₂.underlying decoded
      ; compatible = HigherInput.decoded-triangle Φ ∙ FunctorOverIso₂.compatible decoded }
      where
      decoded : FunctorOverIso₂ (Encoded.decode (Encoded.encode Φ)) Ψ
      decoded = Encoded.decode-into (Encoded.encode Φ) Ψ Ω

  opaque
    unfolding decode-between Encoded.decode-into Encoded.decode-comparison
    decode-underlying : {Φ Ψ : FunctorOverIso u v}
      (Ω : ConeIso (Encoded.encode Φ) (Encoded.encode Ψ)) →
      FunctorOverIso₂.underlying (decode-between Ω) =₃ ConeIso.leftIso Ω
    decode-underlying Ω = idIso _

  opaque
    unfolding HigherInput.Compared.encoded
    encode-underlying : {Φ Ψ : FunctorOverIso u v} (α : FunctorOverIso₂ Φ Ψ) →
      ConeIso.leftIso (HigherInput.Compared.encoded α) =₃ FunctorOverIso₂.underlying α
    encode-underlying α = idIso _

  opaque
    identity : (Φ : FunctorOverIso u v) → FunctorOverIso₂ Φ Φ
    identity Φ = decode-between {Φ = Φ} {Ψ = Φ} (coneIso-id (Encoded.encode Φ))

    compose : {Φ Ψ Ω : FunctorOverIso u v} →
      FunctorOverIso₂ Ψ Ω → FunctorOverIso₂ Φ Ψ → FunctorOverIso₂ Φ Ω
    compose {Φ} {Ψ} {Ω} β α = decode-between {Φ = Φ} {Ψ = Ω}
      (coneIso-compose (HigherInput.Compared.encoded β) (HigherInput.Compared.encoded α))

    inverse : {Φ Ψ : FunctorOverIso u v} → FunctorOverIso₂ Φ Ψ → FunctorOverIso₂ Ψ Φ
    inverse {Φ} {Ψ} α = decode-between {Φ = Ψ} {Ψ = Φ} (coneIso-inverse (HigherInput.Compared.encoded α))

    identity-underlying : (Φ : FunctorOverIso u v) →
      FunctorOverIso₂.underlying (identity Φ) =₃ idIso (FunctorOverIso.underlying Φ)
    identity-underlying Φ = decode-underlying {Φ = Φ} {Ψ = Φ} (coneIso-id (Encoded.encode Φ))

    compose-underlying : {Φ Ψ Ω : FunctorOverIso u v}
      (β : FunctorOverIso₂ Ψ Ω) (α : FunctorOverIso₂ Φ Ψ) →
      FunctorOverIso₂.underlying (compose β α) =₃
        (FunctorOverIso₂.underlying β ∙ FunctorOverIso₂.underlying α)
    compose-underlying {Φ} {Ψ} {Ω} β α = isoComp-cong (encode-underlying β) (encode-underlying α) ∙
      decode-underlying {Φ = Φ} {Ψ = Ω}
        (coneIso-compose (HigherInput.Compared.encoded β) (HigherInput.Compared.encoded α))

    inverse-underlying : {Φ Ψ : FunctorOverIso u v} (α : FunctorOverIso₂ Φ Ψ) →
      FunctorOverIso₂.underlying (inverse α) =₃ (FunctorOverIso₂.underlying α) ⁻¹
    inverse-underlying {Φ} {Ψ} α = (＝-inv ◁ encode-underlying α) ∙
      decode-underlying {Φ = Ψ} {Ψ = Φ} (coneIso-inverse (HigherInput.Compared.encoded α))
```
