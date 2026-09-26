# Recognizing a pullback from lifting and comparison

To prove a cone universal, it suffices to factor the chosen pullback
through it and to reflect comparisons of endomorphisms of its cone point.
The two inverse comparisons use only these specified cone comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.PullbackCriterion
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (pullback-reflect)

opaque
  cone-isPullback-from-lifting : {C D E S : CAT} {f : MAP C E} {g : MAP D E}
    (s : Cone f g S) (inverse : MAP (Pullback f g) S) →
    ConeIso (conePre inverse s) (pullbackCone f g) →
    ((h k : MAP S S) → ConeIso (conePre h s) (conePre k s) → h =₁ k) →
    IsPullback s
  cone-isPullback-from-lifting {S = S} {f = f} {g = g} s inverse β reflect = record
    { inverse = inverse
    ; sectionIso = (reflect (inverse ∘ pullbackLift s) (id S)
        (coneIso-compose (coneIso-inverse (conePre-id s))
          (coneIso-compose (pullbackLift-β s)
            (coneIso-compose (coneIso-pre (pullbackLift s) β)
              (coneIso-inverse (conePre-assoc (pullbackLift s) inverse s)))))) ⁻¹
    ; retractionIso = (pullback-reflect {f = f} {g = g} (pullbackLift s ∘ inverse) (id (Pullback f g))
        (coneIso-compose (coneIso-inverse (conePre-id (pullbackCone f g)))
          (coneIso-compose β (coneIso-compose (coneIso-pre inverse (pullbackLift-β s))
            (coneIso-inverse (conePre-assoc inverse (pullbackLift s) (pullbackCone f g))))))) ⁻¹ }
```
