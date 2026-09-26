# Pullbacks as base changes of the diagonal

This proves `lem:Alternative_Description_Pullbacks` for the direct matching:
pair the original matching with the identity, retaining the product
projection comparisons. Reading the two coordinates recovers the original
cone. This gives the universal property directly and then compares its
matching with the one transported from the chosen diagonal pullback.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Coordinates.DiagonalPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackCriterion 𝒯 P using (cone-isPullback-from-lifting)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.DiagonalCoordinates 𝒯 using (module Coordinates)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.DiagonalRestriction 𝒯 using (module Restriction)

module DiagonalPullback {C D E : CAT} (f : MAP C E) (g : MAP D E) where

  open Coordinates f g
  source = pullbackCone f g
  target = pullbackCone F Δ

  recover-pre : {S T : CAT} (r : MAP S T) (t : Cone F Δ T)
    → ConeIso (from (conePre r t)) (conePre r (from t))
  recover-pre r t = Restriction.comparison f g t r

  recover-direct-pre : {S T : CAT} (r : MAP S T) (s : Cone f g T)
    → ConeIso (from (conePre r (Direct.value s))) (conePre r s)
  recover-direct-pre r s = coneIso-compose (coneIso-pre r (Direct.recover s)) (recover-pre r (Direct.value s))

  module Universal {T : CAT} (s : Cone f g T) (es : IsPullback s) where
    module Original = UniversalCone s es
    direct = Direct.value s
    inverse = Original.factor (from target)

    opaque
      factorization : ConeIso (conePre inverse direct) target
      factorization = from-reflect
        (coneIso-compose (Original.factor-β (from target)) (recover-direct-pre inverse s))

      reflect-comparisons : (h k : MAP T T)
        → ConeIso (conePre h direct) (conePre k direct) → h =₁ k
      reflect-comparisons h k Φ = Original.reflect h k
        (coneIso-compose (recover-direct-pre k s)
          (coneIso-compose (from-iso Φ) (coneIso-inverse (recover-direct-pre h s))))

      isPullback : IsPullback direct
      isPullback = cone-isPullback-from-lifting direct inverse factorization reflect-comparisons

  forward : MAP (Pullback f g) (Pullback F Δ)
  forward = pullbackLift (Direct.value source)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = Universal.isPullback source (pullbackCone-isPullback f g)

  forward-left : (pullback₁ ∘ forward) =₁ (pair (pullback₁ {f = f} {g}) pullback₂)
  forward-left = pullbackLift-β₁ (Direct.value source)

  forward-right : (pullback₂ ∘ forward) =₁ (g ∘ pullback₂ {f = f} {g})
  forward-right = pullbackLift-β₂ (Direct.value source)

  module Square {T : CAT} (s : Cone f g T) where
    module D = Direct s
    value : Cone F Δ T
    value = D.value
    left = Cone.left value
    right = Cone.right value
    induced = forward ∘ pullbackLift s
    original = conePre induced target

    opaque
      source-comparison : ConeIso (conePre (pullbackLift s) (Direct.value source)) value
      source-comparison = from-reflect
        (coneIso-compose (coneIso-inverse D.recover)
          (coneIso-compose (pullbackLift-β s) (recover-direct-pre (pullbackLift s) source)))

      comparison : ConeIso original value
      comparison = coneIso-compose source-comparison
        (coneIso-compose (coneIso-pre (pullbackLift s) (pullbackLift-β (Direct.value source)))
          (coneIso-inverse (conePre-assoc (pullbackLift s) forward target)))

    left-comparison = ConeIso.leftIso comparison
    right-comparison = ConeIso.rightIso comparison
    transported = coneRetarget original left right left-comparison right-comparison

    matching-comparison : (Cone.match transported) =₂ (Cone.match value)
    matching-comparison = coneRetarget-match comparison

    factorization : (pullbackLift value) =₁ induced
    factorization = pullback-η induced ∙ (pullbackLift-cong comparison) ⁻¹

    preserve : IsPullback s → IsPullback value
    preserve es = equiv-transport (factorization ⁻¹) (equiv-compose (pullbackLift s) forward es forward-isEquiv)

    reflect : IsPullback value → IsPullback s
    reflect es = equiv-cancel-left (pullbackLift s) forward forward-isEquiv (equiv-transport factorization es)
```
