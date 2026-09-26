# Testing the slice pullback on a functor category

Apply `Fun X` to the slice definition. The exponential equivalence,
product comparison, and cylinder-coordinate change give its tested
pullback over the two copies of `Fun (X × Y) C`. The lower map factors
through the pair consisting of the variable functor and the fixed `ψ`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval

module SCT.VolumeI.Chapter03.Section07.MappingCalculus.SliceFunctorPullback
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Interval.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (pair-after; productMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.ExponentialLaw 𝒯 M ℱ using (module ExponentialLaw)
open import SCT.VolumeI.Chapter01.Section07.FunctorProducts 𝒯 M ℱ using (module ProductComparison)
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P using (mappedCone)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.Cospans.EquivalentCospanCone 𝒯 P using (module Transport)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneRetarget; coneRetarget-β)
open import SCT.VolumeI.Chapter03.Section07.Slices 𝒯 M ℱ P I using (module Slice; endpoint; endpoints; constantFamily)
open import SCT.VolumeI.Chapter03.Section07.MappingCalculus.SliceCylinderCoordinates 𝒯 I using (insert; module Coordinates)
open import SCT.VolumeI.Chapter03.Section07.MappingCalculus.ExponentialRestriction 𝒯 M ℱ using (module Restriction)
open import SCT.VolumeI.Chapter03.Section07.MappingCalculus.ExponentialConstants 𝒯 M ℱ P using (module Projection; module Fixed)

module Tested (X : CAT) {Y C : CAT} (ψ : MAP Y C) where
  module Defined = Slice ψ using (category; cone; diagram; projection; boundary; functor-square-isPullback)
  module Product = ProductComparison X (Fun Y C) (Fun Y C) using (forward; forward-isEquiv)
  module Exponential = ExponentialLaw X Y C using (forward; forward-isEquiv)
  module Cylinder = ExponentialLaw X ([1] × Y) C using (forward; forward-isEquiv)
  module Coordinates′ = Coordinates X Y using (reorder; reorder-isEquiv; module Endpoint)
  A = Fun X C
  Z = Fun (X × Y) C
  W = Fun ((X × Y) × [1]) C
  inverse-reorder = IsEquiv.inverse Coordinates′.reorder-isEquiv
  upper : MAP (Fun X (Fun ([1] × Y) C)) W
  upper = funPre inverse-reorder ∘ Cylinder.forward
  base : MAP (Fun X (Fun Y C × Fun Y C)) (Z × Z)
  base = productMap Exponential.forward Exponential.forward ∘ Product.forward
  cylinder-endpoints : MAP W (Z × Z)
  cylinder-endpoints = pair (funPre (insert zero)) (funPre (insert one))
  boundary-projections : MAP (A × Fun Y C) (Z × Z)
  boundary-projections = productMap (funPre pr₁) (funPre pr₂)
  fixed : MAP A (A × Fun Y C)
  fixed = pair (id A) (const (nameFun ψ))
  lower : MAP A (Z × Z)
  lower = boundary-projections ∘ fixed
  abstract
    upper-isEquiv : IsEquiv upper
    upper-isEquiv = equiv-compose Cylinder.forward (funPre inverse-reorder) Cylinder.forward-isEquiv
      (funPre-isEquiv inverse-reorder (equiv-inverse Coordinates′.reorder-isEquiv))
    base-isEquiv : IsEquiv base
    base-isEquiv = equiv-compose Product.forward (productMap Exponential.forward Exponential.forward)
      Product.forward-isEquiv (productMap-isEquiv Exponential.forward Exponential.forward
        Exponential.forward-isEquiv Exponential.forward-isEquiv)
    base-pair : {D : CAT} (u v : MAP D (Fun Y C)) →
      (base ∘ funPost (pair u v)) =₁
      pair (Exponential.forward ∘ funPost u) (Exponential.forward ∘ funPost v)
    base-pair u v = pair-after Exponential.forward Exponential.forward (funPost u) (funPost v) ∙
      ((productMap Exponential.forward Exponential.forward ◁
        (pair-cong (funPost-cong (pair-β₁ u v) ∙ funPost-comp (pair u v) pr₁)
          (funPost-cong (pair-β₂ u v) ∙ funPost-comp (pair u v) pr₂) ∙
          pair-pre (funPost pr₁) (funPost pr₂) (funPost (pair u v)))) ∙
        comp-assoc (funPost (pair u v)) Product.forward (productMap Exponential.forward Exponential.forward))
    endpoint-comparison : (e : Obj-abs [1]) →
      (funPre (insert {X = X × Y} e) ∘ upper) =₁
      (Exponential.forward ∘ funPost (funPre (endpoint Y e)))
    endpoint-comparison e = (Restriction.comparison X C (endpoint Y e)) ⁻¹ ∙
      (((funPre-cong (Coordinates′.Endpoint.inverse-comparison e) ∙
        funPre-comp (insert e) inverse-reorder) ▷ Cylinder.forward) ∙
        (comp-assoc Cylinder.forward (funPre inverse-reorder) (funPre (insert e))) ⁻¹)
    upper-square : (cylinder-endpoints ∘ upper) =₁ (base ∘ funPost (endpoints Y C))
    upper-square = (base-pair (funPre (endpoint Y zero)) (funPre (endpoint Y one))) ⁻¹ ∙
      (pair-cong (endpoint-comparison zero) (endpoint-comparison one) ∙
        pair-pre (funPre (insert zero)) (funPre (insert one)) upper)
    lower-normal : (base ∘ funPost Defined.boundary) =₁ lower
    lower-normal =
      (pair-cong (comp-unitʳ (funPre pr₁)) (idIso (funPre pr₂ ∘ const (nameFun ψ))) ∙
        pair-after (funPre pr₁) (funPre pr₂) (id A) (const (nameFun ψ))) ⁻¹ ∙
      (pair-cong (Projection.comparison X Y C) (Fixed.comparison X ψ) ∙
        base-pair (constantFamily Y C) (const (nameFun ψ)))
  cospan : CospanMap (funPost (endpoints Y C)) (funPost Defined.boundary) cylinder-endpoints lower
  cospan = record { left = upper ; right = id A ; base = base
    ; leftSquare = upper-square ; rightSquare = lower-normal ⁻¹ ∙ comp-unitʳ lower }
  module Changed = Transport cospan upper-isEquiv (id-isEquiv A) base-isEquiv
    (mappedCone X Defined.cone) (Defined.functor-square-isPullback X) using (cone; isPullback)
  diagram : MAP (Fun X Defined.category) W
  diagram = upper ∘ funPost Defined.diagram
  projection : MAP (Fun X Defined.category) A
  projection = funPost Defined.projection
  cone : Cone cylinder-endpoints lower (Fun X Defined.category)
  cone = coneRetarget Changed.cone diagram projection (idIso diagram) (comp-unitˡ projection)
  abstract
    isPullback : IsPullback cone
    isPullback = pullback-cone-invariant
      (coneRetarget-β Changed.cone diagram projection (idIso diagram) (comp-unitˡ projection)) Changed.isPullback
```
