# Encoding and decoding cone comparisons

A cone comparison is encoded by a cone of absolute points in the two
leg-isomorphism animae. Decoding respects the entire comparison, including
the next compatibility. Evaluation naturality supplies that compatibility.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup

module SCT.VolumeI.Chapter01.Section05.ConeComparisonEncoding
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.PointEvaluationNaturality 𝒯
open import SCT.VolumeI.Chapter01.Section05.ComparisonSquares 𝒯
  using (transport-square; decode-encode)

module Encoding {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s t : Cone f g T) where

  Left = Cone.left s ＝ Cone.left t
  Right = Cone.right s ＝ Cone.right t
  Middle = (f ∘ Cone.left s) ＝ (g ∘ Cone.right t)
  leftMap : MAP Left Middle
  leftMap = const (Cone.match t) ∙ postWhisker f
  rightMap : MAP Right Middle
  rightMap = postWhisker g ∙ const (Cone.match s)

  leftEvaluation : (α : Obj-abs Left)
    → =₁ (leftMap ∘ α) (Cone.match t ∙ (f ◁ α))
  leftEvaluation α = left-evaluation (Cone.match t) (postWhisker f) α
  rightEvaluation : (β : Obj-abs Right)
    → =₁ (rightMap ∘ β) ((g ◁ β) ∙ Cone.match s)
  rightEvaluation β = right-evaluation (postWhisker g) (Cone.match s) β

  encode : ConeIso s t → Cone leftMap rightMap One
  encode Φ = record
    { left = ConeIso.leftIso Φ
    ; right = ConeIso.rightIso Φ
    ; match = invIso (rightEvaluation (ConeIso.rightIso Φ)) ∙
        (ConeIso.compatible Φ ∙ leftEvaluation (ConeIso.leftIso Φ)) }

  decode : Cone leftMap rightMap One → ConeIso s t
  decode z = record
    { leftIso = Cone.left z
    ; rightIso = Cone.right z
    ; compatible = rightEvaluation (Cone.right z) ∙
        (Cone.match z ∙ invIso (leftEvaluation (Cone.left z))) }

  opaque
    decode-comparison : {z z′ : Cone leftMap rightMap One}
      → ConeIso z z′ → ConeIso₂ (decode z) (decode z′)
    decode-comparison {z} {z′} Ω = record
      { leftId = ConeIso.leftIso Ω
      ; rightId = ConeIso.rightIso Ω
      ; compatible = transport-square {X = One} {Y = Middle}
          (leftEvaluation (Cone.left z)) (leftEvaluation (Cone.left z′))
          (rightEvaluation (Cone.right z)) (rightEvaluation (Cone.right z′))
          (Cone.match z) (Cone.match z′)
          (leftMap ◁ ConeIso.leftIso Ω) (rightMap ◁ ConeIso.rightIso Ω)
          (isoComp-cong (idIso (Cone.match t)) (postWhisker f ◁ ConeIso.leftIso Ω))
          (isoComp-cong (postWhisker g ◁ ConeIso.rightIso Ω) (idIso (Cone.match s)))
          (left-evaluation-natural (Cone.match t) (postWhisker f) (ConeIso.leftIso Ω))
          (right-evaluation-natural (postWhisker g) (Cone.match s) (ConeIso.rightIso Ω))
          (ConeIso.compatible Ω) }
  
  opaque
    decode-into : (z : Cone leftMap rightMap One) (Φ : ConeIso s t)
      → ConeIso z (encode Φ) → ConeIso₂ (decode z) Φ
    decode-into z Φ Ω = record
      { leftId = ConeIso₂.leftId Ξ
      ; rightId = ConeIso₂.rightId Ξ
      ; compatible = ConeIso₂.compatible Ξ ∙
          isoComp-cong (invIso (decode-encode {X = One} {Y = Middle}
            (leftEvaluation (ConeIso.leftIso Φ)) (rightEvaluation (ConeIso.rightIso Φ))
            (ConeIso.compatible Φ)))
            (idIso (isoComp-cong (idIso (Cone.match t)) (postWhisker f ◁ ConeIso₂.leftId Ξ))) }
      where
      Ξ : ConeIso₂ (decode z) (decode (encode Φ))
      Ξ = decode-comparison {z = z} {z′ = encode Φ} Ω
```
