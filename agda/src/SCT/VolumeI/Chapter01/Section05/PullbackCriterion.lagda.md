# Recognizing a pullback from lifting and comparison

To prove a cone universal, it suffices to factor the chosen pullback
through it and to reflect comparisons of endomorphisms of its cone point.
The two inverse comparisons use only these specified cone comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.PullbackCriterion
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.PullbackLifting 𝒯 P using (pullback-reflect)

opaque
  cone-isPullback-from-lifting : {C D E S : CAT} {f : MAP C E} {g : MAP D E}
    (s : Cone f g S) (inverse : MAP (Pullback f g) S) →
    ConeIso (conePre inverse s) (pbCone f g) →
    ((h k : MAP S S) → ConeIso (conePre h s) (conePre k s) → NatIso h k) →
    IsPullback s
  cone-isPullback-from-lifting {S = S} {f = f} {g = g} s inverse β reflect = record
    { inverse = inverse
    ; sectionIso = invIso (reflect (inverse ∘ pbLift s) (id S)
        (coneIso-compose (coneIso-inverse (conePre-id s))
          (coneIso-compose (pbLift-β s)
            (coneIso-compose (coneIso-pre (pbLift s) β)
              (coneIso-inverse (conePre-assoc (pbLift s) inverse s))))))
    ; retractionIso = invIso (pullback-reflect {f = f} {g = g} (pbLift s ∘ inverse) (id (Pullback f g))
        (coneIso-compose (coneIso-inverse (conePre-id (pbCone f g)))
          (coneIso-compose β (coneIso-compose (coneIso-pre inverse (pbLift-β s))
            (coneIso-inverse (conePre-assoc inverse (pbLift s) (pbCone f g))))))) }
```
