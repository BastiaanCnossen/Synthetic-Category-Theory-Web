# Mapping a cone by evaluation and currying

The mapped square is obtained by currying the original cone after
evaluation. Its matching is therefore part of the construction. Uncurrying
transfers the pullback lifting and comparison properties to this square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.MappingCalculus.MappedCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯 M
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (pullback-reflect)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeUncurrying 𝒯 M using (uncurryCone; uncurryConeIso)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeUncurryingPre 𝒯 M using (uncurryCone-restrict)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeCurrying 𝒯 M using (module CurryCone)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeReflection 𝒯 M using (module ReflectCone)
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (post-tests-all)

module MappedCone {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (T : CAT) (s : Cone f g S) where

  module Curried = CurryCone (map-isAn T S) (conePre mapEval s)
  value = Curried.value

  opaque
    evaluate : {X : CAT} (h : MAP X (Map T S)) →
      ConeIso (uncurryCone (conePre h value)) (conePre (mapUncurry h) s)
    evaluate h = coneIso-compose (conePre-assoc (productMap h (id T)) mapEval s)
      (coneIso-compose (coneIso-pre (productMap h (id T)) Curried.comparison)
        (uncurryCone-restrict {f = f} {g = g} h value))

mappedCone : {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (T : CAT) → Cone f g S → Cone (mapPost {C = T} f) (mapPost g) (Map T S)
mappedCone = MappedCone.value

opaque
  mappedCone-iso : {C D E S : CAT} {f : MAP C E} {g : MAP D E}
    (T : CAT) {s t : Cone f g S} → ConeIso s t → ConeIso (mappedCone T s) (mappedCone T t)
  mappedCone-iso {S = S} {f = f} {g = g} T {s} {t} Φ = ReflectCone.comparison {f = f} {g = g}
    (map-isAn T S) (mappedCone T s) (mappedCone T t)
    (coneIso-compose (coneIso-inverse (MappedCone.Curried.comparison T t))
      (coneIso-compose (coneIso-pre mapEval Φ) (MappedCone.Curried.comparison T s)))

opaque
  mappedCone-pre : {C D E S R : CAT} {f : MAP C E} {g : MAP D E}
    (T : CAT) (r : MAP R S) (s : Cone f g S) →
    ConeIso (conePre (mapPost r) (mappedCone T s)) (mappedCone T (conePre r s))
  mappedCone-pre {R = R} {f = f} {g = g} T r s = ReflectCone.comparison {f = f} {g = g} (map-isAn T R)
    (conePre (mapPost r) (mappedCone T s)) (mappedCone T (conePre r s))
    (coneIso-compose (coneIso-inverse (MappedCone.Curried.comparison T (conePre r s)))
      (coneIso-compose (coneIso-inverse (conePre-assoc mapEval r s))
        (coneIso-compose (cone-action s (mapPost-β r)) (MappedCone.evaluate T s (mapPost r)))))

```
