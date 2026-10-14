# Comparisons between factorizations through a pullback square

The comparison of two factorizations is determined by a comparison of
their whole cones. We retain its images under both projections. In
particular, restricting a chosen factorization agrees with factoring
the restricted cone, with the same projection identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.UniversalFactorComparisons
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.UniversalConeLifting 𝒯 P
  using (module UniversalLift)

module At {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (t : Cone f g T) (et : IsPullback t) where
  open UniversalCone t et using (factor; factor-β)

  module Compare {Γ : CAT} (s : Cone f g Γ) (h : MAP Γ T)
    (β : ConeIso (conePre h t) s) where
    prescribed = coneIso-compose (coneIso-inverse β) (factor-β s)
    module Lift = UniversalLift t et (factor s) h prescribed
      using (lift; left-image; right-image)

    comparison : factor s =₁ h
    comparison = Lift.lift

    left-image : (Cone.left t ◁ comparison) =₂ ConeIso.leftIso prescribed
    left-image = Lift.left-image

    right-image : (Cone.right t ◁ comparison) =₂ ConeIso.rightIso prescribed
    right-image = Lift.right-image

  module Congruence {Γ : CAT} {s s′ : Cone f g Γ} (Φ : ConeIso s s′) where
    β = coneIso-compose (coneIso-inverse Φ) (factor-β s′)
    open Compare s (factor s′) β public
      using (comparison; left-image; right-image)

  module Restrict {Γ Δ : CAT} (s : Cone f g Γ) (r : MAP Δ Γ) where
    β : ConeIso (conePre (factor s ∘ r) t) (conePre r s)
    β = coneIso-compose (coneIso-pre r (factor-β s))
      (coneIso-inverse (conePre-assoc r (factor s) t))

    open Compare (conePre r s) (factor s ∘ r) β public
      using (comparison; left-image; right-image)
```
