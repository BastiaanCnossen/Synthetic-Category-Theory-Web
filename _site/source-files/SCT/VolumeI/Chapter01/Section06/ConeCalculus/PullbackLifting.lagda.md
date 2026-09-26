# Lifting a compatible cone comparison

A cone comparison supplies an absolute point in the pullback of the two
leg-isomorphism animae. The inverse of the axiom's specified comparison
functor then gives a natural isomorphism between the original functors.
The resulting computation rule compares the entire cone comparison with
the input, including its compatibility witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.PullbackComparison as Comparison

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open Laws.PullbackStructure P

module Lift {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (h k : MAP T (Pullback f g)) (Φ : ConeIso (conePre h (pullbackCone f g)) (conePre k (pullbackCone f g))) where

  module J = Comparison.IsoComparison 𝒯 dataPullback {f = f} {g = g} h k
  module Encoding = J.A.Boundary
  α = ConeIso.leftIso Φ
  β = ConeIso.rightIso Φ

  pointCone : Cone J.leftMap J.rightMap One
  pointCone = Encoding.encode Φ

  point : Obj-abs J.Target
  point = pullbackLift pointCone

  chosen : FunctorLift J.forward point
  chosen = equiv-lift (pullback-isoMap-isEquiv h k) point

  abstract
    lift : h =₁ k
    lift = FunctorLift.lift chosen

    image : (J.forward ∘ lift) =₁ point
    image = FunctorLift.comparison chosen

  opaque
    restricted-factorization : ConeIso
      (conePre lift (conePre J.forward (pullbackCone J.leftMap J.rightMap)))
      (conePre lift J.comparisonCone)
    restricted-factorization = coneIso-pre lift (pullbackLift-β J.comparisonCone)

  opaque
    associated-factorization : ConeIso
      (conePre lift (conePre J.forward (pullbackCone J.leftMap J.rightMap)))
      (conePre (J.forward ∘ lift) (pullbackCone J.leftMap J.rightMap))
    associated-factorization = conePre-assoc lift J.forward (pullbackCone J.leftMap J.rightMap)

  opaque
    image-action : ConeIso
      (conePre (J.forward ∘ lift) (pullbackCone J.leftMap J.rightMap))
      (conePre point (pullbackCone J.leftMap J.rightMap))
    image-action = cone-action (pullbackCone J.leftMap J.rightMap)
      {h = J.forward ∘ lift} {k = point} image

  opaque
    encoded-image : ConeIso (conePre lift J.comparisonCone) pointCone
    encoded-image = coneIso-compose (pullbackLift-β pointCone)
      (coneIso-compose image-action
      (coneIso-compose associated-factorization (coneIso-inverse restricted-factorization)))

  opaque
    -- Decoding this restricted universal cone is definitionally
    -- cone-action (pullbackCone f g) lift, including its compatibility witness.
    comparison-image : ConeIso₂
      (Encoding.decode (conePre lift J.comparisonCone)) Φ
    comparison-image = Encoding.decode-into (conePre lift J.comparisonCone) Φ encoded-image

  left-image : (pullback₁ {f = f} {g = g} ◁ lift) =₂ α
  left-image = ConeIso₂.leftId comparison-image

  right-image : (pullback₂ {f = f} {g = g} ◁ lift) =₂ β
  right-image = ConeIso₂.rightId comparison-image

pullback-reflect : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (h k : MAP T (Pullback f g))
  → ConeIso (conePre h (pullbackCone f g)) (conePre k (pullbackCone f g)) → h =₁ k
pullback-reflect = Lift.lift
```
