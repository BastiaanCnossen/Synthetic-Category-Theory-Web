# Pullback pasting through a specified comparison

A comparison with the restriction of a pullback cone identifies an outer
rectangle with the pasted rectangle when its first leg is the matching
of the inner square. This criterion retains that matching and does not
require equality of entire cone comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonPasting
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)

module At {A B X Z T V : CAT} (f : MAP A B) (g : MAP B Z) (h : MAP X Z)
  (s : Cone g h V) (es : IsPullback s)
  (r : Cone f (Cone.left s) T) (er : IsPullback r)
  (q : Cone (g ∘ f) h T)
  (same-left : Cone.left q =₁ Cone.left r)
  (Φ : ConeIso (compositeCone f g q) (conePre (Cone.right r) s))
  (frame : ConeIso.leftIso Φ =₂ (Cone.match r ∙ (f ◁ same-left))) where

  module Paste = Pasting f g h s es using (module Paste; paste-isPullback)

  abstract
    comparison : ConeIso q (Paste.Paste.flatten r)
    comparison = compositeCone-compatible f g q (Paste.Paste.flatten r)
      same-left (ConeIso.rightIso raw) (ConeIso.compatible normalized)
      where
      raw : ConeIso (compositeCone f g q) (compositeCone f g (Paste.Paste.flatten r))
      raw = coneIso-compose (coneIso-inverse (Paste.Paste.flatten-composite r)) Φ
      left-normal : ConeIso.leftIso raw =₂ (f ◁ same-left)
      left-normal = isoComp-unitˡ-at (f ◁ same-left) ∙
        (isoComp-cong (isoComp-inverseˡ-at (Cone.match r)) (idIso (f ◁ same-left)) ∙
        ((isoComp-assoc-at ((Cone.match r) ⁻¹) (Cone.match r) (f ◁ same-left)) ⁻¹ ∙
          isoComp-cong (idIso ((Cone.match r) ⁻¹)) frame))
      normalized : ConeIso (compositeCone f g q) (compositeCone f g (Paste.Paste.flatten r))
      normalized = coneIso-adjust raw (f ◁ same-left) (ConeIso.rightIso raw)
        left-normal (idIso _)

    square-isPullback : IsPullback q
    square-isPullback = pullback-cone-invariant (coneIso-inverse comparison)
      (Paste.paste-isPullback r er)
```
