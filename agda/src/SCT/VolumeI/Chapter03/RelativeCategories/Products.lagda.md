# Products over a category

The product over a base is the absolute pullback of the two structure
functors. A pair of functors over the base gives its cone, whose matching
is the composite of the two specified triangles. The induced functor
retains its triangle and the entire pullback comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Products
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P

module Product {C D S : CAT} (f : MAP C S) (g : MAP D S) where
  category = Pullback f g
  projection : MAP category S
  projection = f ∘ pullback₁
  first : FunctorOver projection f
  first = record { lift = pullback₁ ; comparison = idIso projection }
  second : FunctorOver projection g
  second = record { lift = pullback₂ ; comparison = pullbackMatch ⁻¹ }

  module Pair {A : CAT} {h : MAP A S} (u : FunctorOver h f) (v : FunctorOver h g) where
    cone : Cone f g A
    cone = record { left = FunctorLift.lift u ; right = FunctorLift.lift v
      ; match = (FunctorLift.comparison v) ⁻¹ ∙ FunctorLift.comparison u }
    functor : MAP A category
    functor = pullbackLift cone
    abstract
      triangle : (projection ∘ functor) =₁ h
      triangle = FunctorLift.comparison u ∙
        ((f ◁ pullbackLift-β₁ cone) ∙ comp-assoc functor (pullback₁ {f = f} {g}) f)
    over : FunctorOver h projection
    over = record { lift = functor ; comparison = triangle }
    abstract
      comparison : ConeIso (conePre functor (pullbackCone f g)) cone
      comparison = pullbackLift-β cone
```
