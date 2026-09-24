# Mapping out preserves the specified pasting

Uncurrying compares the pasted mapping cone with the pasted product
cocone. Product pasting and evaluation of the outer square then supply
a comparison of whole cocones. Reflection through uncurrying gives the
required cone comparison, including its compatibility with the matchings.
No functor-category structure is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section08.MappingPastingComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.ConeArrowChange 𝒯
  using (changeLeft; changeLeft-iso; changeLeft-pre)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.MapRestrictionCones 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.MapSquareEvaluation 𝒯 M P using (module Evaluation)
open import SCT.VolumeI.Chapter01.Section08.PrecompositionComposition 𝒯 M using (module CompositorEvaluation)
import SCT.VolumeI.Chapter01.Section08.CoconeArrowRestriction as Arrow
import SCT.VolumeI.Chapter01.Section08.ProductRestrictionPasting as Product
import SCT.VolumeI.Chapter01.Section08.UncurryPasting as Uncurry

module Diagram {A₁ A₂ A₃ B₁ B₂ B₃ : CAT}
  {g₁ : MAP A₁ A₂} {g₂ : MAP A₂ A₃}
  {h₁ : MAP B₁ B₂} {h₂ : MAP B₂ B₃}
  {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂} {f₃ : MAP A₃ B₃}
  (left : Square g₁ f₁ f₂ h₁) (right : Square g₂ f₂ f₃ h₂) (E : CAT) where

  X = Map B₃ E
  parameter = id X
  z = mapUncurry parameter
  outer = PastedSquare.outer left right
  t = mappingOut left E
  s = mappingOut right E
  κg = mapPre-comp {D = E} g₁ g₂
  κp = productRestriction-comp X g₁ g₂
  module CP = PasteCones (mapPre {D = E} g₂) (mapPre g₁) t
  module ProductPaste = Product.Action.Pasting 𝒯 M X left right
  module UP = Uncurry.Uncurry 𝒯 M P g₂ left (conePre parameter s)
  module Right = Evaluation right parameter
    (CompositorEvaluation.comparison g₂ f₃ parameter)
    (CompositorEvaluation.comparison f₂ h₂ parameter)
  module Outer = Evaluation outer parameter
    (CompositorEvaluation.comparison (g₂ ∘ g₁) f₃ parameter)
    (CompositorEvaluation.comparison f₁ (h₂ ∘ h₁) parameter)

  source = changeLeft κg (CP.flatten s)
  target = mappingOut outer E
  source₁ = conePre parameter source
  source₂ = changeLeft κg (CP.flatten (conePre parameter s))
  target₁ = conePre parameter target

  source-comparison : ConeIso source₁ source₂
  source-comparison = coneIso-compose
    (changeLeft-iso κg (CP.flatten-pre parameter s))
    (changeLeft-pre κg parameter (CP.flatten s))

  abstract
    restricted-comparison : CoconeIso
      (Arrow.restrict 𝒯 κp (uncurryRestriction {u = g₂ ∘ g₁} {v = f₁} source₁))
      (Arrow.restrict 𝒯 κp (uncurryRestriction {u = g₂ ∘ g₁} {v = f₁} target₁))
    restricted-comparison = coconeIso-compose
      (Arrow.restrict-iso 𝒯 κp (coconeIso-inverse Outer.comparison))
      (coconeIso-compose
        (coconeIso-inverse (Arrow.postcomparison 𝒯 κp z (productCocone X outer)))
      (coconeIso-compose (ProductPaste.postcomparison z)
      (coconeIso-compose (ProductPaste.Paste.flatten-iso Right.comparison)
      (coconeIso-compose UP.comparison
        (Arrow.restrict-iso 𝒯 κp (uncurryRestrictionIso source-comparison))))))

    evaluated-comparison : CoconeIso
      (uncurryRestriction {u = g₂ ∘ g₁} {v = f₁} source₁)
      (uncurryRestriction {u = g₂ ∘ g₁} {v = f₁} target₁)
    evaluated-comparison = Arrow.reflect-iso 𝒯 κp _ _ restricted-comparison

    comparison : ConeIso source target
    comparison = coneIso-compose (conePre-id target)
      (coneIso-compose
        (ReflectRestriction.comparison (map-isAn B₃ E) source₁ target₁ evaluated-comparison)
        (coneIso-inverse (conePre-id source)))
```
