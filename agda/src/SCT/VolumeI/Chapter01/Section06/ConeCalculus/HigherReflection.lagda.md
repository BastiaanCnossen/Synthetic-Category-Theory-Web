# Reflecting higher comparisons through a pullback

A full higher cone comparison can be encoded as a comparison of cones
in the leg-isomorphism animae. Consequently the pullback comparison
reflects it to an identification of the original identifications. Both
leg comparisons and the matching witness are required.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackComparison as Comparison

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.HigherReflection
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeComparisonEncoding 𝒯 using (module Encoding)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
  using (decode-encode; untransport; reflect-transport-square)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PointEvaluationNaturality 𝒯
  using (left-evaluation-natural; right-evaluation-natural)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneIso-compose; coneIso-inverse)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (module UniversalCone)

module Encoded {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s t : Cone f g T) where
  module E = Encoding s t

  opaque
    triangle : (Φ : ConeIso s t) →
      ConeIso.compatible (E.decode (E.encode Φ)) =₃ ConeIso.compatible Φ
    triangle Φ = decode-encode (E.leftEvaluation (ConeIso.leftIso Φ))
      (E.rightEvaluation (ConeIso.rightIso Φ)) (ConeIso.compatible Φ)

    comparison : {Φ Ψ : ConeIso s t} → ConeIso₂ Φ Ψ → ConeIso (E.encode Φ) (E.encode Ψ)
    comparison {Φ} {Ψ} Ξ = record
      { leftIso = ConeIso₂.leftId Ξ ; rightIso = ConeIso₂.rightId Ξ
      ; compatible = reflect-transport-square
          (E.leftEvaluation (ConeIso.leftIso Φ)) (E.leftEvaluation (ConeIso.leftIso Ψ))
          (E.rightEvaluation (ConeIso.rightIso Φ)) (E.rightEvaluation (ConeIso.rightIso Ψ))
          (Cone.match (E.encode Φ)) (Cone.match (E.encode Ψ))
          (E.leftMap ◁ ConeIso₂.leftId Ξ) (E.rightMap ◁ ConeIso₂.rightId Ξ)
          (ConeIso₂.leftBoundary Ξ) (ConeIso₂.rightBoundary Ξ)
          (left-evaluation-natural (Cone.match t) (postWhisker f) (ConeIso₂.leftId Ξ))
          (right-evaluation-natural (postWhisker g) (Cone.match s) (ConeIso₂.rightId Ξ))
          (isoComp-cong (idIso (ConeIso₂.rightBoundary Ξ)) ((triangle Φ) ⁻¹) ∙
            (ConeIso₂.compatible Ξ ∙ isoComp-cong (triangle Ψ) (idIso (ConeIso₂.leftBoundary Ξ)))) }

    normalization : (z : Cone E.leftMap E.rightMap One) → ConeIso (E.encode (E.decode z)) z
    normalization z = cone-match-change _ _ _ _
      (untransport (E.leftEvaluation (Cone.left z)) (E.rightEvaluation (Cone.right z)) (Cone.match z))

    reflect-decoding : {z z′ : Cone E.leftMap E.rightMap One} →
      ConeIso₂ (E.decode z) (E.decode z′) → ConeIso z z′
    reflect-decoding {z} {z′} Ξ = coneIso-compose (normalization z′)
      (coneIso-compose (comparison {Φ = E.decode z} {Ψ = E.decode z′} Ξ)
        (coneIso-inverse (normalization z)))

module Reflection {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (h k : MAP T (Pullback f g)) where
  module Compared = Comparison.IsoComparison 𝒯 dataPullback h k
    using (comparisonCone; module A)
  module Enc = Encoded (conePre h (pullbackCone f g)) (conePre k (pullbackCone f g))
    using (reflect-decoding)
  module Universal = UniversalCone Compared.comparisonCone (pullback-isoMap-isEquiv h k)
    using (reflect)

  -- This is cone-action on the defining pullback cone. Keeping the
  -- universal comparison cone named avoids expanding its matching.
  induced-cone : (α : h =₁ k) →
    ConeIso (conePre h (pullbackCone f g)) (conePre k (pullbackCone f g))
  induced-cone α = Compared.A.Boundary.decode (conePre α Compared.comparisonCone)

  opaque
    reflect : {α β : h =₁ k} →
      ConeIso₂ (induced-cone α) (induced-cone β) → α =₂ β
    reflect {α} {β} Ξ = Universal.reflect {S = One} α β
      (Enc.reflect-decoding {z = conePre α Compared.comparisonCone}
        {z′ = conePre β Compared.comparisonCone} Ξ)
```
