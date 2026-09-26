# The transferred identification-anima equivalence

For a pullback square, transport the chosen pullback's identification-anima
equivalence through its comparison equivalence. Both projection functors are
identified with postwhiskering by the original legs. Retargeting along those
identifications specifies the full matching and preserves the equivalence.

This proves the transfer with its transported matching. Agreement with the
independently specified matching in `ConeAction.Action` is a separate
obligation in `SCT.Investigations.PullbackComparisonCoherence`. No extra
coherence is assumed here.

The main declarations are in `Transfer`: `comparison` is the functor,
`comparison-isEquiv` proves it is an equivalence, and `computation` compares
its entire cone with the specified projection cone, including the transported
matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.PullbackComparison as Comparison
import SCT.VolumeI.Chapter01.Section06.Coordinates.UniversalConeProjectionCalculus as ProjectionCalculus

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.UniversalConeComparison
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open ProjectionCalculus 𝒯 P public using (composite-projection)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeComparisonEncoding 𝒯 using (module Encoding)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeIdentificationTransport 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (module CospanMap)

```

## Comparing the given square with the chosen pullback

The pullback comparison `l` is an equivalence. Its computation comparison
identifies the two cones after restriction along either `h` or `k`.
These cone identifications determine `Change`, the equivalence between
the two pullbacks of identification animae.

```agda
module Transfer {C D E T S : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) (es : IsPullback s) (h k : MAP S T) where

  l = pullbackLift s
  β = pullbackLift-β s
  p = Cone.left s
  q = Cone.right s

  compare-left : (r : MAP S T) → (pullback₁ ∘ (l ∘ r)) =₁ (p ∘ r)
  compare-left r = (ConeIso.leftIso β ▷ r) ∙ (comp-assoc r l pullback₁) ⁻¹

  compare-right : (r : MAP S T) → (pullback₂ ∘ (l ∘ r)) =₁ (q ∘ r)
  compare-right r = (ConeIso.rightIso β ▷ r) ∙ (comp-assoc r l pullback₂) ⁻¹

  opaque
    compare-compatible : (r : MAP S T) →
      (Cone.match (conePre r s) ∙ (f ◁ compare-left r)) =₂
      ((g ◁ compare-right r) ∙ Cone.match (conePre (l ∘ r) (pullbackCone f g)))
    compare-compatible r = ConeIso.compatible
      (coneIso-compose (coneIso-pre r β)
        (coneIso-inverse (conePre-assoc r l (pullbackCone f g))))

  compare : (r : MAP S T) →
    ConeIso (conePre (l ∘ r) (pullbackCone f g)) (conePre r s)
  compare r = record
    { leftIso = compare-left r ; rightIso = compare-right r
    ; compatible = compare-compatible r }

  module Chosen = Comparison.IsoComparison 𝒯 dataPullback (l ∘ h) (l ∘ k)
  module Change = Transport (compare h) (compare k)
  module Boundary = Encoding (conePre h s) (conePre k s)

  Target : CAT
  Target = Pullback Boundary.leftMap Boundary.rightMap

  l-whisker : MAP (h ＝ k) ((l ∘ h) ＝ (l ∘ k))
  l-whisker = postWhisker l

  target-left : MAP Target Boundary.Left
  target-left = pullback₁ {f = Boundary.leftMap} {g = Boundary.rightMap}

  target-right : MAP Target Boundary.Right
  target-right = pullback₂ {f = Boundary.leftMap} {g = Boundary.rightMap}

  chosen-left : MAP Chosen.Target Chosen.Left
  chosen-left = pullback₁ {f = Chosen.leftMap} {g = Chosen.rightMap}

  chosen-right : MAP Chosen.Target Chosen.Right
  chosen-right = pullback₂ {f = Chosen.leftMap} {g = Chosen.rightMap}

  abstract
    chosen-comparison : MAP ((l ∘ h) ＝ (l ∘ k)) Chosen.Target
    chosen-comparison = Chosen.forward

    chosen-isEquiv : IsEquiv chosen-comparison
    chosen-isEquiv = pullback-isoMap-isEquiv (l ∘ h) (l ∘ k)

    chosen-left-image : (chosen-left ∘ chosen-comparison) =₁
      (postWhisker {f = l ∘ h} {g = l ∘ k} (pullback₁ {f = f} {g = g}))
    chosen-left-image = pullbackLift-β₁ Chosen.comparisonCone

    chosen-right-image : (chosen-right ∘ chosen-comparison) =₁
      (postWhisker {f = l ∘ h} {g = l ∘ k} (pullback₂ {f = f} {g = g}))
    chosen-right-image = pullbackLift-β₂ Chosen.comparisonCone

```

## Transferring the equivalence

First postwhisker by `l`, then apply the chosen pullback's comparison, and
finally transport along `Change`. Each of these three functors is an
equivalence. The argument establishing this remains explicit below.

```agda
  source-map : MAP (h ＝ k) Chosen.Target
  source-map = chosen-comparison ∘ l-whisker

  forward : MAP (h ＝ k) Target
  forward = Change.pullbackMap ∘ source-map

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = equiv-compose source-map Change.pullbackMap
    (equiv-compose l-whisker chosen-comparison
      (postWhisker-isEquiv l es h k) chosen-isEquiv)
    Change.equivalence

```

## Identifying the two projections

The calculation in `UniversalConeProjectionCalculus` identifies the
transported projections with postwhiskering by the original cone legs.
Here we apply it to each leg and paste with the two projection comparisons
of the chosen pullback.

```agda
  module Projection = ProjectionCalculus.Projection 𝒯 P l h k

  opaque
    left-normalized :
      (Change.Left.forward ∘ (postWhisker {f = l ∘ h} {g = l ∘ k} (pullback₁ {f = f} {g = g}) ∘ l-whisker)) =₁
      (postWhisker {f = h} {g = k} p)
    left-normalized = Projection.normalize (pullback₁ {f = f} {g = g}) p (ConeIso.leftIso β)

    right-normalized :
      (Change.Right.forward ∘ (postWhisker {f = l ∘ h} {g = l ∘ k} (pullback₂ {f = f} {g = g}) ∘ l-whisker)) =₁
      (postWhisker {f = h} {g = k} q)
    right-normalized = Projection.normalize (pullback₂ {f = f} {g = g}) q (ConeIso.rightIso β)

    left-projection : (target-left ∘ forward) =₁ (postWhisker {f = h} {g = k} p)
    left-projection = left-normalized ∙
      composite-projection l-whisker chosen-comparison Change.pullbackMap
        chosen-left target-left (postWhisker {f = l ∘ h} {g = l ∘ k} (pullback₁ {f = f} {g = g})) Change.Left.forward
        chosen-left-image
        Change.left-projection

    right-projection : (target-right ∘ forward) =₁ (postWhisker {f = h} {g = k} q)
    right-projection = right-normalized ∙
      composite-projection l-whisker chosen-comparison Change.pullbackMap
        chosen-right target-right (postWhisker {f = l ∘ h} {g = l ∘ k} (pullback₂ {f = f} {g = g})) Change.Right.forward
        chosen-right-image
        Change.right-projection

```

## Retaining the matching and the computation comparison

Restrict the target pullback cone along `forward`, then retarget its legs
using the projection identifications. This specifies `comparisonCone` and
its transported `matching`. Invariance of the pullback property proves
that its factorization is an equivalence; the factorization's beta
comparison supplies the full cone computation.

```agda
  rawCone : Cone Boundary.leftMap Boundary.rightMap (h ＝ k)
  rawCone = conePre forward (pullbackCone Boundary.leftMap Boundary.rightMap)

  comparisonCone : Cone Boundary.leftMap Boundary.rightMap (h ＝ k)
  comparisonCone = coneRetarget rawCone (postWhisker {f = h} {g = k} p) (postWhisker {f = h} {g = k} q)
    left-projection right-projection

  -- This is the full transported matching, not just its two projections.
  matching : (Boundary.leftMap ∘ postWhisker {f = h} {g = k} p) =₁
    (Boundary.rightMap ∘ postWhisker {f = h} {g = k} q)
  matching = Cone.match comparisonCone

  opaque
    comparisonCone-isPullback : IsPullback comparisonCone
    comparisonCone-isPullback = pullback-cone-invariant
      (coneRetarget-β rawCone (postWhisker {f = h} {g = k} p) (postWhisker {f = h} {g = k} q)
        left-projection right-projection)
      (pullback-restrict-equivalence (pullbackCone Boundary.leftMap Boundary.rightMap)
        forward (pullbackCone-isPullback Boundary.leftMap Boundary.rightMap) forward-isEquiv)

  comparison : MAP (h ＝ k) Target
  comparison = pullbackLift comparisonCone

  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = comparisonCone-isPullback

  computation : ConeIso
    (conePre comparison (pullbackCone Boundary.leftMap Boundary.rightMap)) comparisonCone
  computation = pullbackLift-β comparisonCone
```
