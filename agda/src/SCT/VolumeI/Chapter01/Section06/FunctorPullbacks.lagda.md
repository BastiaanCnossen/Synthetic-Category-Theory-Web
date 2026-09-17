# Functor categories preserve pullbacks

The mapped square is obtained by currying the original cone after
evaluation. Its matching is therefore part of the construction. Uncurrying
transfers the pullback lifting and comparison properties to this square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.FunctorPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M)
  (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.IsomorphismLifting 𝒯 M ℱ
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.PullbackCriterion 𝒯 P using (cone-isPullback-from-lifting)
open import SCT.VolumeI.Chapter01.Section05.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.PullbackLifting 𝒯 P using (pullback-reflect)
open import SCT.VolumeI.Chapter01.Section06.ConeUncurrying 𝒯 M ℱ using (uncurryCone; uncurryConeIso)
open import SCT.VolumeI.Chapter01.Section06.ConeUncurryingPre 𝒯 M ℱ using (uncurryCone-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCurrying 𝒯 M ℱ using (module CurryCone)
open import SCT.VolumeI.Chapter01.Section06.ConeReflection 𝒯 M ℱ using (module ReflectCone)


open import SCT.VolumeI.Chapter01.Section06.MappedCones 𝒯 M ℱ P public

module FunctorPullback {C D E : CAT} (T : CAT) (f : MAP C E) (g : MAP D E) where

  S = Fun T (Pullback f g)
  F = funPost {C = T} f
  G = funPost {C = T} g
  R = Pullback F G
  original : Cone f g (Pullback f g)
  original = pbCone f g
  square : Cone F G S
  square = mappedCone T original

  module LiftCone {X : CAT} (s : Cone F G X) where
    uncurried : Cone f g (X × T)
    uncurried = uncurryCone {f = f} {g = g} s
    raw : MAP (X × T) (Pullback f g)
    raw = pbLift uncurried
    lift : MAP X S
    lift = funCurry raw

    abstract
      comparison : ConeIso (conePre lift square) s
      comparison = ReflectCone.comparison {f = f} {g = g} (conePre lift square) s
        (coneIso-compose (pbLift-β uncurried)
          (coneIso-compose (cone-action original (funCurry-β raw)) (MappedCone.evaluate T original lift)))

  opaque
    reflect : {X : CAT} → (h k : MAP X S) →
      ConeIso (conePre h square) (conePre k square) → NatIso h k
    reflect h k Φ = funIsoReflect h k (pullback-reflect {f = f} {g = g} (funUncurry h) (funUncurry k)
      (coneIso-compose (MappedCone.evaluate T original k)
        (coneIso-compose (uncurryConeIso {f = f} {g = g} Φ) (coneIso-inverse (MappedCone.evaluate T original h)))))

  comparison : MAP S R
  comparison = pbLift square
  module Inverse = LiftCone (pbCone F G)
  inverse : MAP R S
  inverse = Inverse.lift

  opaque
    square-isPullback : IsPullback square
    square-isPullback = cone-isPullback-from-lifting square inverse Inverse.comparison
      reflect

```

