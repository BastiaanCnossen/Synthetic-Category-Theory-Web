# Agreement with the direct interchange matching

The full transferred equivalence is proved in `UniversalConeComparison`.
This investigation isolates the additional comparison with the matching
specified independently by `ConeAction.Action`. Its premise is not proved
or made an axiom. In particular, the conditional result below must not be
reported as establishing the direct comparison unconditionally.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.Investigations.PullbackComparisonCoherence
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeAction 𝒯 using (module Action)
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.UniversalConeComparison 𝒯 P

module DirectComparison {C D E T S : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) (es : IsPullback s) (h k : MAP S T) where

  module Transferred = Transfer s es h k
  module Direct = Action s h k

  MatchingAgreement : Set m
  MatchingAgreement = Transferred.matching =₂ Direct.matching

  direct-comparison-isEquiv : MatchingAgreement → IsEquiv (pullbackLift Direct.universal)
  direct-comparison-isEquiv agreement = pullback-cone-invariant
    (cone-match-change (postWhisker {f = h} {g = k} (Cone.left s))
      (postWhisker {f = h} {g = k} (Cone.right s))
      Transferred.matching Direct.matching agreement)
    Transferred.comparisonCone-isPullback
```
