# The anima of relative identifications

Keep an identification and its triangle witness together as a point of
a pullback of isomorphism animae. An identification in this pullback
decodes to a full comparison of relative identifications, including the
dimension-three compatibility. This is the data needed by the higher
computation rule for relative family lifting.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonEncoding
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PointEvaluationNaturality 𝒯
  using (left-evaluation; left-evaluation-natural; const-evaluate-natural)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
  using (transport-square; decode-encode)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left; cancel-right)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (pullbackLift-cong; pullback-η)

module Encoding {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u v : FunctorOver f g) where
  h = FunctorLift.lift u
  k = FunctorLift.lift v
  θu = FunctorLift.comparison u
  θv = FunctorLift.comparison v
  Left = h ＝ k
  Middle = (g ∘ h) ＝ f
  leftMap : MAP Left Middle
  leftMap = const θv ∙ postWhisker g
  rightMap : MAP One Middle
  rightMap = const θu
  category : CAT
  category = Pullback leftMap rightMap
  category-isAn : isAn category
  category-isAn = pullback-isAn leftMap rightMap (＝-isAn h k) one-isAn (＝-isAn (g ∘ h) f)
  leftEvaluation : (α : Obj-abs Left) → (leftMap ∘ α) =₁ (θv ∙ (g ◁ α))
  leftEvaluation α = left-evaluation θv (postWhisker g) α
  rightEvaluation : (β : Obj-abs One) → (rightMap ∘ β) =₁ θu
  rightEvaluation β = const-evaluate θu β
  encode : FunctorOverIso u v → Cone leftMap rightMap One
  encode Φ = record { left = FunctorOverIso.underlying Φ ; right = id One
    ; match = rightEvaluation (id One) ⁻¹ ∙
        (FunctorOverIso.compatible Φ ∙ leftEvaluation (FunctorOverIso.underlying Φ)) }
  decode : Cone leftMap rightMap One → FunctorOverIso u v
  decode z = record { underlying = Cone.left z
    ; compatible = rightEvaluation (Cone.right z) ∙
        (Cone.match z ∙ leftEvaluation (Cone.left z) ⁻¹) }

  module Normalize (z : Cone leftMap rightMap One) where
    L = leftEvaluation (Cone.left z)
    R = rightEvaluation (Cone.right z)
    R₀ = rightEvaluation (id One)
    δ = terminal-iso (Cone.right z) (id One)
    opaque
      recovered : (FunctorOverIso.compatible (decode z) ∙ L) =₂ (R ∙ Cone.match z)
      recovered = isoComp-cong (idIso R)
        (isoComp-unitʳ-at (Cone.match z) ∙
          (isoComp-cong (idIso (Cone.match z)) (isoComp-inverseˡ-at L) ∙
            isoComp-assoc-at (Cone.match z) (L ⁻¹) L)) ∙
        isoComp-assoc-at R (Cone.match z ∙ L ⁻¹) L
      right-image : (rightMap ◁ δ) =₂ (R₀ ⁻¹ ∙ R)
      right-image = isoComp-cong (idIso (R₀ ⁻¹))
        (isoComp-unitˡ-at R ∙ const-evaluate-natural θu δ) ∙
        (cancel-left R₀ (rightMap ◁ δ)) ⁻¹
    opaque
      comparison : ConeIso z (encode (decode z))
      comparison = record { leftIso = idIso (Cone.left z) ; rightIso = δ
        ; compatible = isoComp-cong (right-image ⁻¹) (idIso (Cone.match z)) ∙
          ((isoComp-assoc-at (R₀ ⁻¹) R (Cone.match z)) ⁻¹ ∙
          (isoComp-cong (idIso (R₀ ⁻¹)) recovered ∙
          (isoComp-unitʳ-at (Cone.match (encode (decode z))) ∙
            isoComp-cong (idIso (Cone.match (encode (decode z))))
              (postWhisker-idIso leftMap (Cone.left z))))) }
  opaque
    decode-comparison : {z z′ : Cone leftMap rightMap One} → ConeIso z z′ →
      FunctorOverIso₂ (decode z) (decode z′)
    decode-comparison {z} {z′} Ω = record
      { underlying = ConeIso.leftIso Ω
      ; compatible = isoComp-unitˡ-at (FunctorOverIso.compatible (decode z)) ∙
          transport-square
            (leftEvaluation (Cone.left z)) (leftEvaluation (Cone.left z′))
            (rightEvaluation (Cone.right z)) (rightEvaluation (Cone.right z′))
            (Cone.match z) (Cone.match z′)
            (leftMap ◁ ConeIso.leftIso Ω) (rightMap ◁ ConeIso.rightIso Ω)
            (isoComp-cong (idIso θv) (postWhisker g ◁ ConeIso.leftIso Ω)) (idIso θu)
            (left-evaluation-natural θv (postWhisker g) (ConeIso.leftIso Ω))
            (const-evaluate-natural θu (ConeIso.rightIso Ω)) (ConeIso.compatible Ω) }
    decode-into : (z : Cone leftMap rightMap One) (Φ : FunctorOverIso u v) →
      ConeIso z (encode Φ) → FunctorOverIso₂ (decode z) Φ
    decode-into z Φ Ω = record
      { underlying = FunctorOverIso₂.underlying Ξ
      ; compatible = FunctorOverIso₂.compatible Ξ ∙
          isoComp-cong
            ((decode-encode (leftEvaluation (FunctorOverIso.underlying Φ))
              (rightEvaluation (id One)) (FunctorOverIso.compatible Φ)) ⁻¹)
            (idIso (isoComp-cong (idIso θv) (postWhisker g ◁ FunctorOverIso₂.underlying Ξ))) }
      where
      Ξ : FunctorOverIso₂ (decode z) (decode (encode Φ))
      Ξ = decode-comparison {z = z} {z′ = encode Φ} Ω
  point : FunctorOverIso u v → Obj-abs category
  point Φ = pullbackLift (encode Φ)
  value : Obj-abs category → FunctorOverIso u v
  value x = decode (conePre x (pullbackCone leftMap rightMap))
  opaque
    point-computation : (Φ : FunctorOverIso u v) → FunctorOverIso₂ (value (point Φ)) Φ
    point-computation Φ = decode-into _ Φ (pullbackLift-β (encode Φ))
    value-computation : (x : Obj-abs category) → x =₁ point (value x)
    value-computation x = pullbackLift-cong (Normalize.comparison (conePre x (pullbackCone leftMap rightMap))) ∙
      (pullback-η x) ⁻¹
```
