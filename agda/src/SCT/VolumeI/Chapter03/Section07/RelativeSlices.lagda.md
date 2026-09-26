# Relative slices and coslices

For the absolute base-parametrized assertions in `cons:General_Slice_Category`
and `con:Contextual_Slice_Categories`, take the dependent product of the
relative arrow category along the exponentiable source projection.
Its two evaluations induce the endpoint functors. Relative currying
constructs the constant family and the section determined by the diagram.

The slice and coslice are the displayed pullbacks, with the two lower
components in the respective orders. Their specified matching and
projection to the base are retained. No categorical-context inheritance
is asserted here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval

module SCT.VolumeI.Chapter03.Section07.RelativeSlices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Interval.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullbackCone-isPullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.ExponentiableFunctors 𝒯 M ℱ P using (IsExponentiable; module Exponentiable)
open import SCT.VolumeI.Chapter03.Section05.InternalFunctors 𝒯 M ℱ P using (module FunctorCategory)
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target)
open import SCT.VolumeI.Chapter03.Section05.DependentProductAction 𝒯 M ℱ P using (module Induced)
open import SCT.VolumeI.Chapter03.RelativeCategories.Products 𝒯 M ℱ P using (module Product)
open import SCT.VolumeI.Chapter03.Section07.MappingCalculus.RelativeArrows 𝒯 M ℱ P using (module Diagrams)

module Construction {C Y Γ : CAT} (pC : MAP C Γ) (pY : MAP Y Γ)
  (epY : IsExponentiable pY) (ψ : FunctorOver pY pC) where
  A = Pullback pC pY
  r : MAP A Y
  r = pullback₂
  module Internal = FunctorCategory pY pC epY
  module Curry = Currying.Native pY r Internal.product
  module Arrows = Diagrams [1] r
  arrow-product = Exponentiable.dependent-product epY Arrows.projection
  arrow-category = DependentProduct.category arrow-product
  arrow-projection = DependentProduct.projection arrow-product
  module Endpoint (e : Obj-abs [1]) = Induced pY Arrows.projection r
    arrow-product Internal.product (Arrows.At.over e)
  module Pairing = Product Internal.projection Internal.projection
  endpoints : FunctorOver arrow-projection Pairing.projection
  endpoints = Pairing.Pair.over (Endpoint.over zero) (Endpoint.over one)

  constant : FunctorOver pC Internal.projection
  constant = Curry.factor pC (identity-over r)

  unit-projection : MAP (Pullback (id Γ) pY) Y
  unit-projection = pullback₂
  projected : FunctorOver (pY ∘ unit-projection) pY
  projected = record { lift = unit-projection ; comparison = idIso (pY ∘ unit-projection) }
  section : FunctorOver (id Γ) Internal.projection
  section = Curry.factor (id Γ)
    (Target.backward pY pC unit-projection (compose-over ψ projected))
  to-base : FunctorOver pC (id Γ)
  to-base = record { lift = pC ; comparison = comp-unitˡ pC }
  fixed : FunctorOver pC Internal.projection
  fixed = compose-over section to-base

  module Boundary (left right : FunctorOver pC Internal.projection) where
    boundary : FunctorOver pC Pairing.projection
    boundary = Pairing.Pair.over left right
    upper = FunctorLift.lift endpoints
    lower = FunctorLift.lift boundary
    category : CAT
    category = Pullback upper lower
    projection : MAP category Γ
    projection = pC ∘ pullback₂
    diagram : MAP category arrow-category
    diagram = pullback₁
    forget : MAP category C
    forget = pullback₂
    matching : (upper ∘ diagram) =₁ (lower ∘ forget)
    matching = pullbackMatch
    abstract
      diagram-triangle : (arrow-projection ∘ diagram) =₁ projection
      diagram-triangle = (FunctorLift.comparison boundary ▷ forget) ∙
        ((comp-assoc forget lower Pairing.projection) ⁻¹ ∙
          ((Pairing.projection ◁ matching) ∙
            (comp-assoc diagram upper Pairing.projection ∙
              ((FunctorLift.comparison endpoints ▷ diagram) ⁻¹))))
      universal : IsPullback (pullbackCone upper lower)
      universal = pullbackCone-isPullback upper lower

  module Slice = Boundary constant fixed
  module Coslice = Boundary fixed constant
```
