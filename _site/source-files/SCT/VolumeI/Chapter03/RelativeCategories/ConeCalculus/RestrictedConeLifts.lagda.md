# Restricting a lifted cone over its right leg

A comparison from a restricted cone to a new cone induces a comparison
of their lifts. The specified right-leg comparison is precisely the
triangle used to restrict the old lift, so the lifted comparison is
over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.RestrictedConeLifts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle; module ToCone)

module Restriction {X Y C D S : CAT} {g : MAP C S} {p : MAP D S}
  (s : Cone g p Y) (t : Cone g p X) (u : FunctorOver (Cone.right t) (Cone.right s))
  (Φ : ConeIso (conePre (FunctorLift.lift u) s) t)
  (image : ConeIso.rightIso Φ =₂ FunctorLift.comparison u) where
  r = FunctorLift.lift u
  over = compose-over (lift-triangle s) u
  cones = coneIso-compose Φ
    (coneIso-compose (coneIso-pre r (pullbackLift-β s))
      (coneIso-inverse (conePre-assoc r (pullbackLift s) (pullbackCone g p))))
  abstract
    right-comparison : ConeIso.rightIso cones =₂ FunctorLift.comparison over
    right-comparison = isoComp-cong image
      (idIso ((pullbackLift-β₂ s ▷ r) ∙ (comp-assoc r (pullbackLift s) (pullback₂ {f = g} {p})) ⁻¹))

    comparison : FunctorOverIso over (lift-triangle t)
    comparison = ToCone.comparison t over cones right-comparison
```
