# Pullback cancellation from a cone comparison

A comparison with the restriction of a pullback cone determines the inner
square of a pasted diagram. If the outer cone is a pullback, that inner
square is a pullback as well. The construction retains the prescribed
left leg of the comparison as its matching isomorphism.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonCancellation
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯
  using (changeLeft; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (pre-inverse; inverse-inverse)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)

module At {A B X Z T V : CAT} (f : MAP A B) (g : MAP B Z) (h : MAP X Z)
  (s : Cone g h V) (es : IsPullback s)
  (q : Cone (g ∘ f) h T) (eq : IsPullback q) (e : MAP T V)
  (Φ : ConeIso (conePre e s) (compositeCone f g q)) where

  module Paste = Pasting f g h s es using (module Paste; cancel-isPullback)
  α = ConeIso.leftIso Φ
  β = ConeIso.rightIso Φ

  square : Cone f (Cone.left s) T
  square = record { left = Cone.left q ; right = e ; match = α ⁻¹ }

  abstract
    outer-comparison : ConeIso (Paste.Paste.flatten square) q
    outer-comparison = compositeCone-compatible f g (Paste.Paste.flatten square) q
      (idIso (Cone.left q)) β (ConeIso.compatible normalized)
      where
      raw : ConeIso (compositeCone f g (Paste.Paste.flatten square)) (compositeCone f g q)
      raw = coneIso-compose Φ (Paste.Paste.flatten-composite square)
      normalized : ConeIso (compositeCone f g (Paste.Paste.flatten square)) (compositeCone f g q)
      normalized = coneIso-adjust raw (f ◁ idIso (Cone.left q)) β
        ((postWhisker-idIso f (Cone.left q)) ⁻¹ ∙ isoComp-inverseʳ-at α)
        (isoComp-unitʳ-at β)

    square-isPullback : IsPullback square
    square-isPullback = Paste.cancel-isPullback square
      (pullback-cone-invariant (coneIso-inverse outer-comparison) eq)

module Framed {A B X Z T V : CAT} (f : MAP A B) (g : MAP B Z) (h : MAP X Z)
  {v : MAP A Z} (κ : (g ∘ f) =₁ v)
  (s : Cone g h V) (es : IsPullback s)
  (q : Cone v h T) (eq : IsPullback q) where

  p = Cone.left q
  b = Cone.right q
  δ = Cone.match q

  outer : Cone (g ∘ f) h T
  outer = record { left = p ; right = b ; match = δ ∙ (κ ▷ p) }

  edge-cone : Cone g h T
  edge-cone = record { left = f ∘ p ; right = b
    ; match = δ ∙ ((κ ▷ p) ∙ (comp-assoc p f g) ⁻¹) }

  abstract
    outer-isPullback : IsPullback outer
    outer-isPullback = pullback-cone-invariant
      (cone-match-change _ _ _ _
        (isoComp-cong (idIso δ) (inverse-inverse (κ ▷ p) ∙ (＝-inv ◁ pre-inverse κ p))))
      (ChangeLeft.preserve (κ ⁻¹) h q eq)

  module WithComparison (e : MAP T V) (Φ : ConeIso (conePre e s) edge-cone) where
    composite-comparison : ConeIso (conePre e s) (compositeCone f g outer)
    composite-comparison = record
      { leftIso = ConeIso.leftIso Φ ; rightIso = ConeIso.rightIso Φ
      ; compatible = ConeIso.compatible Φ ∙
          isoComp-cong (isoComp-assoc-at δ (κ ▷ p) ((comp-assoc p f g) ⁻¹))
            (idIso (g ◁ ConeIso.leftIso Φ)) }

    open At f g h s es outer outer-isPullback e composite-comparison public
      using (square; square-isPullback)
```
