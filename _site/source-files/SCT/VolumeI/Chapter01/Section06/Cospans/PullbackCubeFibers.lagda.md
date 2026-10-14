# Fibers of a pullback cube

Fiber interchange applies to arbitrary chosen presentations of the top
and bottom pullbacks. A whole cube comparison determines the comparison
between their maps to the canonical pullbacks. Its lifted matching retains
the entire cube through the existing `FactorWithSource` computation.

The resulting fiber cone uses the component fibers of the canonically
represented bottom family. Comparisons with a differently framed family
or with a previously specified fiber cone remain separate obligations.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.PullbackCubeFibers
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences as Equivalences
import SCT.VolumeI.Chapter01.Section06.Cospans.Fibers as Fibers
import SCT.VolumeI.Chapter01.Section06.Cospans.FiberInterchange as FiberInterchange

private
  transport-restriction : {C D E X Y Z : CAT} {f : MAP C E} {g : MAP D E}
    (t : Cone f g Z) (s : Cone f g Y) (q : Cone f g X)
    (a : MAP Y Z) (b : MAP X Y) (c : MAP X Z) →
    ConeIso (conePre a t) s → (a ∘ b) =₁ c → ConeIso (conePre c t) q →
    ConeIso (conePre b s) q
  transport-restriction t s q a b c Φ θ Ψ = coneIso-compose Ψ
    (coneIso-compose (cone-action t θ)
      (coneIso-compose (conePre-assoc b a t) (coneIso-inverse (coneIso-pre b Φ))))

module Cube {C D E C′ D′ E′ S T : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (s : Cone f g S) (t : Cone f′ g′ T)
  (h : MAP S T) (cube : ConeIso (conePre h t) (CospanMap.mapCone F s)) where
  source-comparison : MAP S (Pullback f g)
  source-comparison = pullbackLift s
  target-comparison : MAP T (Pullback f′ g′)
  target-comparison = pullbackLift t
  private
    module Represented = Fibers.At 𝒯 P F target-comparison using (module FactorWithSource)
    family-comparison : ConeIso (CospanMap.mapCone F s)
      (conePre h (conePre target-comparison (pullbackCone f′ g′)))
    family-comparison = coneIso-compose
      (coneIso-pre h (coneIso-inverse (pullbackLift-β t))) (coneIso-inverse cube)
    module CubeLift = Represented.FactorWithSource s h family-comparison
      source-comparison (pullbackLift-β s) using (comparison; comparison-image; prescribed)

  comparison : (CospanMap.pullbackMap F ∘ source-comparison) =₁ (target-comparison ∘ h)
  comparison = CubeLift.comparison
  open CubeLift public using (comparison-image)

  module At {Γ : CAT} (x : MAP Γ T) where
    represented-family : MAP Γ (Pullback f′ g′)
    represented-family = target-comparison ∘ x
    family-computation : ConeIso
      (conePre represented-family (pullbackCone f′ g′)) (conePre x t)
    family-computation = coneIso-compose (coneIso-pre x (pullbackLift-β t))
      (coneIso-inverse (conePre-assoc x target-comparison (pullbackCone f′ g′)))
    fiber-cospan : CospanMap h x (CospanMap.pullbackMap F) represented-family
    fiber-cospan = record
      { left = source-comparison ; right = id Γ ; base = target-comparison
      ; leftSquare = comparison ; rightSquare = comp-unitʳ represented-family }
    to-represented-fiber : MAP (Pullback h x) (Pullback (CospanMap.pullbackMap F) represented-family)
    to-represented-fiber = CospanMap.pullbackMap fiber-cospan
    to-represented-fiber-computation : ConeIso
      (conePre to-represented-fiber (pullbackCone (CospanMap.pullbackMap F) represented-family))
      (CospanMap.mapCone fiber-cospan (pullbackCone h x))
    to-represented-fiber-computation = CospanMap.pullbackMap-β fiber-cospan

    private
      module Components = Fibers.At 𝒯 P F represented-family
        using (left-family; right-family; base-family; matching; left-fiber; right-fiber; base-fiber; left-map; right-map)
    open Components public
      using (left-family; right-family; base-family; matching; left-fiber; right-fiber; base-fiber; left-map; right-map)

    module Universal (es : IsPullback s) (et : IsPullback t) where
      private
        module FiberEquivalence = Equivalences.CospanEquivalence 𝒯 P fiber-cospan
          es (id-isEquiv Γ) et using (pullbackMap-isEquiv)
        module Interchange = FiberInterchange.At 𝒯 P F represented-family
          using (component-pullback; component-pullback-cone; fiber-comparison; fiber-comparison-isEquiv;
            fiber-cone; fiber-comparison-computation)

      to-represented-fiber-isEquiv : IsEquiv to-represented-fiber
      to-represented-fiber-isEquiv = FiberEquivalence.pullbackMap-isEquiv

      private
        chosen : FunctorLift Interchange.fiber-comparison to-represented-fiber
        chosen = equiv-lift Interchange.fiber-comparison-isEquiv to-represented-fiber

      component-map-calculation : MAP (Pullback h x) Interchange.component-pullback
      component-map-calculation = FunctorLift.lift chosen

      abstract
        to-component-pullback : MAP (Pullback h x) Interchange.component-pullback
        to-component-pullback = component-map-calculation
        to-component-pullback-computation : to-component-pullback =₁ component-map-calculation
        to-component-pullback-computation = idIso component-map-calculation

        factor-comparison : (Interchange.fiber-comparison ∘ to-component-pullback) =₁ to-represented-fiber
        factor-comparison = FunctorLift.comparison chosen

        to-component-pullback-isEquiv : IsEquiv to-component-pullback
        to-component-pullback-isEquiv = equiv-cancel-left to-component-pullback
          Interchange.fiber-comparison Interchange.fiber-comparison-isEquiv
          (equiv-transport (factor-comparison ⁻¹) to-represented-fiber-isEquiv)

      cone : Cone Components.left-map Components.right-map (Pullback h x)
      cone = conePre to-component-pullback Interchange.component-pullback-cone
      isPullback : IsPullback cone
      isPullback = pullback-restrict-equivalence Interchange.component-pullback-cone
        to-component-pullback (pullbackCone-isPullback Components.left-map Components.right-map)
        to-component-pullback-isEquiv

      fiber-computation :
        ConeIso (conePre to-component-pullback Interchange.fiber-cone)
          (CospanMap.mapCone fiber-cospan (pullbackCone h x))
      fiber-computation = transport-restriction
        (pullbackCone (CospanMap.pullbackMap F) represented-family)
        Interchange.fiber-cone (CospanMap.mapCone fiber-cospan (pullbackCone h x))
        Interchange.fiber-comparison to-component-pullback to-represented-fiber
        Interchange.fiber-comparison-computation factor-comparison to-represented-fiber-computation
```
