# Mapping animae preserve and detect pullback squares

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

module SCT.VolumeI.Chapter01.Section06.MappingPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯 M
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackCriterion 𝒯 P using (cone-isPullback-from-lifting)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (pullback-reflect)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeUncurrying 𝒯 M using (uncurryCone; uncurryConeIso)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeUncurryingPre 𝒯 M using (uncurryCone-restrict)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeCurrying 𝒯 M using (module CurryCone)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeReflection 𝒯 M using (module ReflectCone)
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (post-tests-all)

open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.MappedCones 𝒯 M P public

module MappingPullback {C D E : CAT} (T : CAT) (f : MAP C E) (g : MAP D E) where

  S = Map T (Pullback f g)
  F = mapPost {C = T} f
  G = mapPost {C = T} g
  R = Pullback F G
  original : Cone f g (Pullback f g)
  original = pullbackCone f g
  square : Cone F G S
  square = mappedCone T original

  module LiftCone {X : CAT} (xAn : isAn X) (s : Cone F G X) where
    uncurried : Cone f g (X × T)
    uncurried = uncurryCone {f = f} {g = g} s
    raw : MAP (X × T) (Pullback f g)
    raw = pullbackLift uncurried
    lift : MAP X S
    lift = mapCurry xAn raw

    abstract
      comparison : ConeIso (conePre lift square) s
      comparison = ReflectCone.comparison {f = f} {g = g} xAn (conePre lift square) s
        (coneIso-compose (pullbackLift-β uncurried)
          (coneIso-compose (cone-action original (mapCurry-β xAn raw)) (MappedCone.evaluate T original lift)))

  opaque
    reflect : {X : CAT} → isAn X → (h k : MAP X S) →
      ConeIso (conePre h square) (conePre k square) → h =₁ k
    reflect xAn h k Φ = mapReflect xAn h k (pullback-reflect {f = f} {g = g} (mapUncurry h) (mapUncurry k)
      (coneIso-compose (MappedCone.evaluate T original k)
        (coneIso-compose (uncurryConeIso {f = f} {g = g} Φ) (coneIso-inverse (MappedCone.evaluate T original h)))))

  comparison : MAP S R
  comparison = pullbackLift square
  module Inverse = LiftCone (pullback-isAn F G (map-isAn T C) (map-isAn T D) (map-isAn T E)) (pullbackCone F G)
  inverse : MAP R S
  inverse = Inverse.lift

  opaque
    square-isPullback : IsPullback square
    square-isPullback = cone-isPullback-from-lifting square inverse Inverse.comparison
      (reflect (map-isAn T (Pullback f g)))

mappedCone-factorization : {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (T : CAT) (s : Cone f g S) →
  (pullbackLift (mappedCone T s)) =₁ (pullbackLift (mappedCone T (pullbackCone f g)) ∘ mapPost (pullbackLift s))
mappedCone-factorization {f = f} {g} T s = pullbackLift-restrict (mapPost (pullbackLift s)) (mappedCone T (pullbackCone f g)) ∙
  (pullbackLift-cong (coneIso-compose (mappedCone-iso T (pullbackLift-β s))
    (mappedCone-pre T (pullbackLift s) (pullbackCone f g)))) ⁻¹

map-preserves-pullback : {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (T : CAT) (s : Cone f g S) → IsPullback s → IsPullback (mappedCone T s)
map-preserves-pullback {f = f} {g} T s es = equiv-transport ((mappedCone-factorization T s) ⁻¹)
  (equiv-compose (mapPost (pullbackLift s)) (pullbackLift (mappedCone T (pullbackCone f g)))
    (mapPost-isEquiv (pullbackLift s) es) (MappingPullback.square-isPullback T f g))

map-detects-pullback : {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g S) → ((T : CAT) → IsPullback (mappedCone T s)) → IsPullback s
map-detects-pullback {f = f} {g} s tests = post-tests-all (pullbackLift s) (λ T →
  equiv-cancel-left (mapPost (pullbackLift s)) (pullbackLift (mappedCone T (pullbackCone f g)))
    (MappingPullback.square-isPullback T f g)
    (equiv-transport (mappedCone-factorization T s) (tests T)))
```
