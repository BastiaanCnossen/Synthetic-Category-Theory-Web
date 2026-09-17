# Lifting a compatible cone comparison

A cone comparison supplies an absolute point in the pullback of the two
leg-isomorphism animae. The inverse of the axiom's specified comparison
functor then gives a natural isomorphism between the original functors.
The resulting computation rule compares the entire cone comparison with
the input, including its compatibility witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section05.PullbackComparison as Comparison

module SCT.VolumeI.Chapter01.Section05.PullbackLifting
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section05.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open Laws.PullbackStructure P

module Lift {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (h k : MAP T (Pullback f g)) (Φ : ConeIso (conePre h (pbCone f g)) (conePre k (pbCone f g))) where

  module J = Comparison.IsoComparison 𝒯 dataPullback {f = f} {g = g} h k
  module Encoding = J.A.Boundary
  α = ConeIso.leftIso Φ
  β = ConeIso.rightIso Φ

  pointCone : Cone J.leftMap J.rightMap One
  pointCone = Encoding.encode Φ

  point : ObjAbs J.Target
  point = pbLift pointCone

  chosen : FunctorLift J.forward point
  chosen = equiv-lift (pullback-isoMap-isEquiv h k) point

  abstract
    lift : NatIso h k
    lift = FunctorLift.lift chosen

    image : NatIso (J.forward ∘ lift) point
    image = FunctorLift.comparison chosen

  opaque
    restricted-factorization : ConeIso
      (conePre lift (conePre J.forward (pbCone J.leftMap J.rightMap)))
      (conePre lift J.comparisonCone)
    restricted-factorization = coneIso-pre lift (pbLift-β J.comparisonCone)

  opaque
    associated-factorization : ConeIso
      (conePre lift (conePre J.forward (pbCone J.leftMap J.rightMap)))
      (conePre (J.forward ∘ lift) (pbCone J.leftMap J.rightMap))
    associated-factorization = conePre-assoc lift J.forward (pbCone J.leftMap J.rightMap)

  opaque
    image-action : ConeIso
      (conePre (J.forward ∘ lift) (pbCone J.leftMap J.rightMap))
      (conePre point (pbCone J.leftMap J.rightMap))
    image-action = cone-action (pbCone J.leftMap J.rightMap)
      {h = J.forward ∘ lift} {k = point} image

  opaque
    encoded-image : ConeIso (conePre lift J.comparisonCone) pointCone
    encoded-image = coneIso-compose (pbLift-β pointCone)
      (coneIso-compose image-action
      (coneIso-compose associated-factorization (coneIso-inverse restricted-factorization)))

  opaque
    -- Decoding this restricted universal cone is definitionally
    -- cone-action (pbCone f g) lift, including its compatibility witness.
    comparison-image : ConeIso₂
      (Encoding.decode (conePre lift J.comparisonCone)) Φ
    comparison-image = Encoding.decode-into (conePre lift J.comparisonCone) Φ encoded-image

  left-image : Iso₂ (pb₁ {f = f} {g = g} ◁ lift) α
  left-image = ConeIso₂.leftId comparison-image

  right-image : Iso₂ (pb₂ {f = f} {g = g} ◁ lift) β
  right-image = ConeIso₂.rightId comparison-image

pullback-reflect : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (h k : MAP T (Pullback f g))
  → ConeIso (conePre h (pbCone f g)) (conePre k (pbCone f g)) → NatIso h k
pullback-reflect = Lift.lift
```
