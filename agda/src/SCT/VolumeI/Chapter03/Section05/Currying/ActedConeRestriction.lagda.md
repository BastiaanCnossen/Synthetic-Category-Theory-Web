# Restriction after acting on a cone

Acting with a functor over the base commutes with a specified cone
restriction. Lifting the resulting comparison gives an identification
over the right leg, with its original triangle retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.ActedConeRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.RestrictedConeLifts 𝒯 M ℱ P using (module Restriction)

module Restrict {C D B S X Y : CAT} {f : MAP C B} {g : MAP D B} {p : MAP S B}
  (u : FunctorOver f g) (s : Cone f p Y) (t : Cone f p X)
  (v : FunctorOver (Cone.right t) (Cone.right s))
  (Φ : ConeIso (conePre (FunctorLift.lift v) s) t)
  (image : ConeIso.rightIso Φ =₂ FunctorLift.comparison v) where
  module Act = Action {C = C} {D = D} {S = S} {T = B} {f = f} {g = g} p u
  cones : ConeIso (conePre (FunctorLift.lift v) (Act.value s)) (Act.value t)
  cones = coneIso-compose (Act.map-iso Φ) (Act.restriction (FunctorLift.lift v) s)
  abstract
    right-image : ConeIso.rightIso cones =₂ FunctorLift.comparison v
    right-image = image ∙ isoComp-unitʳ-at (ConeIso.rightIso Φ)

    comparison : FunctorOverIso (compose-over (lift-triangle (Act.value s)) v) (lift-triangle (Act.value t))
    comparison = Restriction.comparison {X = X} {Y = Y} {C = D} {D = S} {S = B} {g = g} {p = p}
      (Act.value s) (Act.value t) v cones right-image
```
