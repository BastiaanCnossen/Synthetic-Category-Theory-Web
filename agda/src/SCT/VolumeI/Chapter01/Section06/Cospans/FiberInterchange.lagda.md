# Fibers commute with pullbacks of cospans

For a map of cospans and a family in the target pullback, the pullback
of the component fibers is equivalent to the fiber of the induced
pullback functor. We paste the cartesian squares of the two preceding
modules and retain the resulting cone and its complete computation.

This is a specified new fiber cone. It does not assert that the earlier
comparison and reconstruction in `Fibers` are inverse, or identify their
chosen matching with the matching obtained by this pasting.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.FiberInterchange
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange as ArrowChange
import SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeSquares as BaseChange
import SCT.VolumeI.Chapter01.Section06.PastingLemma as Pasting
import SCT.VolumeI.Chapter01.Section06.Cospans.Fibers as Fibers
import SCT.VolumeI.Chapter01.Section06.Cospans.FiberInterchangeProjections as Projections
import SCT.VolumeI.Chapter01.Section06.Cospans.FiberInterchangeSquare as Square

module At {C D E C′ D′ E′ Γ : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (x : MAP Γ (Pullback f′ g′)) where
  private
    module F = CospanMap F using (pullbackMap)
    module Fib = Fibers.At 𝒯 P F x using (left-map; right-map; left-family; right-family)

  private
    module Projection = Projections.At 𝒯 P F x
      using (to-base; to-target; right-map; section; section-identification; direct-component-map; component-map-identification; direct-component-square; direct-component-square-isPullback; intermediate; intermediate-cone; source-image; source-computation; to-source; composite-cone; direct-component-computation; target-leg-cone; section-computation)
    open Projection
    module Middle = Square.At 𝒯 P F x using (intermediate-map; intermediate-square; intermediate-square-isPullback; intermediate-factor-computation)
    open Middle
    r = Cone.right intermediate-cone

  component-pullback : CAT
  component-pullback = Pullback Fib.left-map Fib.right-map
  component-pullback-cone : Cone Fib.left-map Fib.right-map component-pullback
  component-pullback-cone = pullbackCone Fib.left-map Fib.right-map

  private
    module Component = BaseChange.Along 𝒯 P Fib.left-map to-base intermediate-cone
      (pullbackCone-isPullback Fib.left-map to-base) direct-component-map component-map-identification
      component-pullback-cone (pullbackCone-isPullback Fib.left-map Fib.right-map)
      using (factor; factor-computation; square; square-isPullback)
    module ComponentPaste = Pasting.Pasting 𝒯 P r right-map section
      direct-component-square direct-component-square-isPullback using (module Paste; paste-isPullback)

  component-to-intermediate : MAP component-pullback intermediate
  component-to-intermediate = Component.factor
  component-to-intermediate-computation = Component.factor-computation

  component-intermediate-square : Cone intermediate-map section component-pullback
  component-intermediate-square = ComponentPaste.Paste.flatten Component.square
  component-intermediate-square-isPullback : IsPullback component-intermediate-square
  component-intermediate-square-isPullback = ComponentPaste.paste-isPullback Component.square Component.square-isPullback

  private
    module TotalPaste = BaseChange.Successive 𝒯 P F.pullbackMap to-target intermediate-square section
      component-intermediate-square using (composite; composite-isPullback)
    module FamilyChange = ArrowChange.ChangeLeft 𝒯 P section-identification F.pullbackMap using (preserve)

  fiber-cone : Cone F.pullbackMap x component-pullback
  fiber-cone = coneSwap (changeLeft section-identification (coneSwap TotalPaste.composite))
  fiber-cone-isPullback : IsPullback fiber-cone
  fiber-cone-isPullback = pullback-swap _
    (FamilyChange.preserve (coneSwap TotalPaste.composite)
      (pullback-swap TotalPaste.composite
        (TotalPaste.composite-isPullback intermediate-square-isPullback component-intermediate-square-isPullback)))

  fiber-comparison : MAP component-pullback (Pullback F.pullbackMap x)
  fiber-comparison = pullbackLift fiber-cone
  fiber-comparison-isEquiv : IsEquiv fiber-comparison
  fiber-comparison-isEquiv = fiber-cone-isPullback
  fiber-comparison-computation :
    ConeIso (conePre fiber-comparison (pullbackCone F.pullbackMap x)) fiber-cone
  fiber-comparison-computation = pullbackLift-β fiber-cone


  source-cone-computation :
    ConeIso (conePre (Cone.left fiber-cone) (pullbackCone f g))
      (conePre component-to-intermediate source-image)
  source-cone-computation = coneIso-compose
    (coneIso-pre component-to-intermediate source-computation)
    (coneIso-inverse (conePre-assoc component-to-intermediate to-source (pullbackCone f g)))

  private
    A = pullbackCone (CospanMap.left F) Fib.left-family
    B = pullbackCone (CospanMap.right F) Fib.right-family
    n₁ = Cone.left component-pullback-cone
    n₂ = Cone.right component-pullback-cone
    j = component-to-intermediate
    l = Cone.left intermediate-cone
    left-factor = ConeIso.rightIso component-to-intermediate-computation
    χ = ConeIso.leftIso component-to-intermediate-computation

  left-arrow-computation :
    (Cone.left (pullbackCone f g) ∘ Cone.left fiber-cone) =₁ (Cone.left A ∘ n₁)
  left-arrow-computation = (Cone.left A ◁ left-factor) ∙
    (comp-assoc j l (Cone.left A) ∙ ConeIso.leftIso source-cone-computation)

  right-arrow-computation :
    (Cone.right (pullbackCone f g) ∘ Cone.left fiber-cone) =₁ (Cone.left B ∘ n₂)
  right-arrow-computation = (ConeIso.leftIso direct-component-computation ▷ n₂) ∙
    ((comp-assoc n₂ direct-component-map (Cone.left composite-cone)) ⁻¹ ∙
    ((Cone.left composite-cone ◁ χ) ∙
      (comp-assoc j r (Cone.left composite-cone) ∙ ConeIso.rightIso source-cone-computation)))

  right-parameter-computation : Cone.right fiber-cone =₁ (Cone.right B ∘ n₂)
  right-parameter-computation = idIso _

  private
    b = Cone.right target-leg-cone
    base = Cone.right B ∘ n₂
    component-parameter : (b ∘ (intermediate-map ∘ j)) =₁ base
    component-parameter = comp-unitˡ base ∙
      ((ConeIso.rightIso section-computation ▷ base) ∙
      ((comp-assoc base section b) ⁻¹ ∙ (b ◁ Cone.match component-intermediate-square)))

  left-parameter-computation : Cone.right fiber-cone =₁ (Cone.right A ∘ n₁)
  left-parameter-computation = (Cone.right A ◁ left-factor) ∙
    (comp-assoc j l (Cone.right A) ∙
    ((ConeIso.rightIso intermediate-factor-computation ▷ j) ∙
    ((comp-assoc j intermediate-map b) ⁻¹ ∙ component-parameter ⁻¹)))
```

The arrow and parameter coordinates do not yet identify the component
fiber cones. That stronger statement also needs compatibility with the
matching of the newly pasted fiber cone.
