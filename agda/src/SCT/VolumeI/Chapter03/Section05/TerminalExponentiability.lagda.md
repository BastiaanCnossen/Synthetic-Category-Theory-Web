# The terminal functor is exponentiable

For `prop:map_to_the_point_is exponentiable`, every pullback of the
terminal functor is equivalent over its base to a product projection.
The product construction supplies dependent products of arbitrary
targets. Transport along the source equivalence supplies them for the
specified pullback square; base-change stability gives Beck–Chevalley.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.TerminalExponentiability
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullback-comparison)
open import SCT.VolumeI.Chapter01.Section06.PullbackProducts 𝒯 P using (module TerminalBase; coneIso-over-One)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.ExponentiableFunctors 𝒯 M ℱ P using (IsExponentiable; module Exponentiable)
open import SCT.VolumeI.Chapter03.Section05.ExponentiabilityCriterion 𝒯 M ℱ P using (from-dependent-products)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductDependentProducts 𝒯 M ℱ P using (module AlongProjection)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.DependentProductSourceTransport 𝒯 M ℱ P using (module Source)

module Terminal (S : CAT) where
  module AfterBaseChange {S′ T : CAT} (b : MAP T One)
    (square : Cone (terminate S) b S′) (square-isPullback : IsPullback square) where
    h = Cone.left square
    p′ = Cone.right square
    e = pair p′ h
    module Product = TerminalBase b (terminate S)
    abstract
      source-isEquiv : IsEquiv e
      source-isEquiv = pullback-comparison (coneSwap square) Product.productCone e
        (coneIso-over-One _ _ (pair-β₁ p′ h) (pair-β₂ p′ h))
        (pullback-swap square square-isPullback) Product.productCone-isPullback

    projection-square : Cone (pr₁ {T} {S}) (id T) S′
    projection-square = record { left = e ; right = p′
      ; match = (comp-unitˡ p′) ⁻¹ ∙ pair-β₁ p′ h }
    abstract
      projection-square-isPullback : IsPullback projection-square
      projection-square-isPullback = degenerate-pullback (id-isEquiv T) projection-square source-isEquiv

    dependent-product : {C : CAT} (f : MAP C S′) → DependentProduct p′ f
    dependent-product f = Source.dependent-product (pr₁ {T} {S}) (id T)
      projection-square projection-square-isPullback source-isEquiv f
      (AlongProjection.dependent-product (e ∘ f))

  abstract
    isExponentiable : IsExponentiable (terminate S)
    isExponentiable = from-dependent-products (terminate S) AfterBaseChange.dependent-product

  dependent-product : {C : CAT} (f : MAP C S) → DependentProduct (terminate S) f
  dependent-product = Exponentiable.dependent-product isExponentiable
```
