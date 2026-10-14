# The outside frame of a restricted precomposition component

The identity endpoint of the parameter-change comparison evaluates to
the outside frame. Its chosen identity evaluation then cancels to the
uncurried left unitor of the precomposition functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionRestrictedOuterFrame
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section04.Substitution.RetainedIdentityParameterChange 𝒯 M using (pair-projections-post)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite; inverse-inverse)
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.SeparationEndpointTransport as Separation
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedUnitSquare as UnitSquare
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedRightUnit as RightUnit
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.UncurryingUnits as Units
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {C D : CAT} (K : CAT) (r : MAP D C) where
  X = Fun C K
  Y = Fun D K
  L : MAP X Y
  L = funPre r
  σ : MAP (X × D) (Y × D)
  σ = productMap L (id D)
  W : MAP (X × D) (X × C)
  W = productMap (id X) r
  e : MAP (X × C) K
  e = funEval
  d : MAP (Y × D) K
  d = funEval
  β : (d ∘ σ) =₁ (e ∘ W)
  β = funPre-β r
  module Product = Separation.Identity 𝒯 M {A = D} L
  z : MAP (X × D) (X × D)
  z = pair pr₁ pr₂
  v : MAP (Y × D) (Y × D)
  v = pair pr₁ pr₂
  ν = Product.Changed.ν
  δ = pair-cong (comp-unitˡ (pr₁ {X} {D})) (idIso (r ∘ pr₂ {X} {D}))
  χ = δ ∙ productMap-pair (id X) r pr₁ pr₂
  outside = (e ◁ δ) ∙ β
  T₀ = comp-unitʳ d ∙ (d ◁ pair-projections)
  tU = comp-unitʳ (d ∘ σ) ∙ ((d ∘ σ) ◁ pair-projections)
  changed = (comp-assoc z σ d) ⁻¹ ∙ ((d ◁ ν) ∙ comp-assoc σ v d)
  n = (e ◁ χ) ∙ (comp-assoc z W e ∙ (β ▷ z))
  Ξ = n ∙ changed
  Ω = outside ∙ (T₀ ▷ σ)
  module Right = RightUnit.At 𝒯 z pair-projections W e β

  abstract
    reversed-square : (Product.left ∙ ν ⁻¹) =₂ Product.right
    reversed-square = cancel-right ν Product.right ∙
      isoComp-cong (Product.unit-square ⁻¹) (idIso (ν ⁻¹))

  module Unit = UnitSquare.At 𝒯 z v pair-projections pair-projections σ (ν ⁻¹) reversed-square d (idIso (d ∘ σ))

  abstract
    right-core : (tU ∙ (comp-assoc z σ d) ⁻¹) =₂ (d ◁ Product.right)
    right-core = cancel-right (comp-assoc z σ d) (d ◁ Product.right) ∙
      isoComp-cong (Unit.right-prefix ⁻¹) (idIso ((comp-assoc z σ d) ⁻¹))

    changed-value : (tU ∙ changed) =₂ (T₀ ▷ σ)
    changed-value = Unit.left-prefix ⁻¹ ∙
      isoComp-cong ((postWhisker d ◁ Product.unit-square) ∙ (postWhisker-isoComp-at d Product.right ν) ⁻¹)
        (idIso (comp-assoc σ v d)) ∙
      (isoComp-assoc-at (d ◁ Product.right) (d ◁ ν) (comp-assoc σ v d)) ⁻¹ ∙
      isoComp-cong right-core (idIso ((d ◁ ν) ∙ comp-assoc σ v d)) ∙
      (isoComp-assoc-at tU ((comp-assoc z σ d) ⁻¹) ((d ◁ ν) ∙ comp-assoc σ v d)) ⁻¹

    coordinate-normal : χ =₂ (δ ∙ Right.right)
    coordinate-normal = isoComp-cong (idIso δ) ((pair-projections-post (id X) r) ⁻¹)

    n-value : n =₂ (outside ∙ tU)
    n-value = Right.changed-output δ χ coordinate-normal

    value : Ξ =₂ Ω
    value = isoComp-cong (idIso outside) changed-value ∙
      isoComp-assoc-at outside tU changed ∙ isoComp-cong n-value (idIso changed)

  tD = funUncurry-id D K
  unit-source = (tD ⁻¹ ∙ T₀) ⁻¹
  module Uncurried = Units.At 𝒯 M ℱ L

  abstract
    identity-cancel : (T₀ ∙ unit-source) =₂ tD
    identity-cancel = inverse-inverse tD ∙ cancel-inverse T₀ (tD ⁻¹ ⁻¹) ∙
      isoComp-cong (idIso T₀) (inverse-composite (tD ⁻¹) T₀)

    prefix : (Ω ∙ (unit-source ▷ σ)) =₂ (outside ∙ (tD ▷ σ))
    prefix = isoComp-cong (idIso outside) (preWhisker σ ◁ identity-cancel) ∙
      isoComp-cong (idIso outside) ((preWhisker-isoComp-at T₀ unit-source σ) ⁻¹) ∙
      isoComp-assoc-at outside (T₀ ▷ σ) (unit-source ▷ σ)

    unit-value : (Ω ∙ ((unit-source ▷ σ) ∙ funUncurry-restrict (id Y) L)) =₂
      (outside ∙ funUncurryIso (comp-unitˡ L))
    unit-value = isoComp-cong (idIso outside) (Uncurried.left ⁻¹) ∙
      isoComp-assoc-at outside (tD ▷ σ) (funUncurry-restrict (id Y) L) ∙
      isoComp-cong prefix (idIso (funUncurry-restrict (id Y) L)) ∙
      (isoComp-assoc-at Ω (unit-source ▷ σ) (funUncurry-restrict (id Y) L)) ⁻¹
```
