# Lifting cones along a split pullback comparison

Suppose the comparison from a cone to the chosen pullback has a section.
Every other cone then factors through the given cone. Unlike a pullback
universal property, this gives existence of a factorization without
uniqueness. The comparison with the input is nevertheless a comparison
of whole cones, including their matching identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.SplitComparisonLifts
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)

module Split {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (t : Cone f g T) (s : MAP (Pullback f g) T)
  (section : (pullbackLift t ∘ s) =₁ id (Pullback f g)) where

  private
    p = pullbackLift t
    universal = pullbackCone f g

  module At {Γ : CAT} (q : Cone f g Γ) where
    factor : MAP Γ T
    factor = s ∘ pullbackLift q

    comparison : (p ∘ factor) =₁ pullbackLift q
    comparison = comp-unitˡ (pullbackLift q) ∙
      ((section ▷ pullbackLift q) ∙ (comp-assoc (pullbackLift q) s p) ⁻¹)

    factor-β : ConeIso (conePre factor t) q
    factor-β = coneIso-compose (pullbackLift-β q)
      (coneIso-compose (cone-action universal comparison)
        (coneIso-compose (conePre-assoc factor p universal)
          (coneIso-inverse (coneIso-pre factor (pullbackLift-β t)))))

    restrict : {Δ : CAT} (r : MAP Δ Γ) →
      (s ∘ pullbackLift (conePre r q)) =₁ (factor ∘ r)
    restrict r = (comp-assoc r (pullbackLift q) s) ⁻¹ ∙
      (s ◁ pullbackLift-restrict r q)

  congruence : {Γ : CAT} {q q′ : Cone f g Γ} → ConeIso q q′ →
    At.factor q =₁ At.factor q′
  congruence Φ = s ◁ pullbackLift-cong Φ
```
