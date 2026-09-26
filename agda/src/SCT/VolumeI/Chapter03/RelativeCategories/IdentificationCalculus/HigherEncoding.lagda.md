# Encoding higher comparisons of relative identifications

A comparison retaining the triangle witness determines an identification
of the corresponding points of the comparison anima. Normalize its two
boundaries, reflect the compatibility square through that normalization,
and apply the pullback comparison. Thus a full native higher comparison
can be used by constructions defined on the whole encoding anima.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.HigherEncoding
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (pullbackLift-cong)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PointEvaluationNaturality 𝒯
  using (left-evaluation-natural; const-evaluate-natural)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
  using (decode-encode; reflect-transport-square)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonEncoding 𝒯 M ℱ P using (module Encoding)

module Higher {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u v : FunctorOver f g) where
  module Encoded = Encoding u v
  θu = FunctorLift.comparison u
  θv = FunctorLift.comparison v

  opaque
    decoded-triangle : (Φ : FunctorOverIso u v) →
      FunctorOverIso.compatible (Encoded.decode (Encoded.encode Φ)) =₃ FunctorOverIso.compatible Φ
    decoded-triangle Φ = decode-encode
      (Encoded.leftEvaluation (FunctorOverIso.underlying Φ))
      (Encoded.rightEvaluation (id One)) (FunctorOverIso.compatible Φ)

  module Compared {Φ Ψ : FunctorOverIso u v} (Ξ : FunctorOverIso₂ Φ Ψ) where
    δ = FunctorOverIso₂.underlying Ξ
    boundary = isoComp-cong (idIso θv) (postWhisker g ◁ δ)
    source = Encoded.encode Φ
    target = Encoded.encode Ψ

    opaque
      decoded-square :
        (FunctorOverIso.compatible (Encoded.decode target) ∙ boundary) =₃
        (idIso θu ∙ FunctorOverIso.compatible (Encoded.decode source))
      decoded-square = isoComp-cong (idIso (idIso θu)) ((decoded-triangle Φ) ⁻¹) ∙
        ((isoComp-unitˡ-at (FunctorOverIso.compatible Φ)) ⁻¹ ∙
        (FunctorOverIso₂.compatible Ξ ∙
          isoComp-cong (decoded-triangle Ψ) (idIso boundary)))

    opaque
      encoded : ConeIso source target
      encoded = record { leftIso = δ ; rightIso = idIso (id One)
        ; compatible = reflect-transport-square
            (Encoded.leftEvaluation (FunctorOverIso.underlying Φ))
            (Encoded.leftEvaluation (FunctorOverIso.underlying Ψ))
            (Encoded.rightEvaluation (id One)) (Encoded.rightEvaluation (id One))
            (Cone.match source) (Cone.match target)
            (Encoded.leftMap ◁ δ) (Encoded.rightMap ◁ idIso (id One))
            boundary (idIso θu)
            (left-evaluation-natural θv (postWhisker g) δ)
            (const-evaluate-natural θu (idIso (id One))) decoded-square }

  opaque
    point-comparison : {Φ Ψ : FunctorOverIso u v} → FunctorOverIso₂ Φ Ψ →
      Encoded.point Φ =₁ Encoded.point Ψ
    point-comparison Ξ = pullbackLift-cong (Compared.encoded Ξ)
```
