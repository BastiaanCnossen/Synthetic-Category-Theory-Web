# The constant-family universal property in manuscript coordinates

For `exercise:Description_Mapping_Object_Over_Gamma`, interchange the
product factors and replace the displayed product by the chosen pullback.
The resulting equivalence uses exactly the source family `D × Γ → Γ`.
Each coordinate change is an equivalence over the base. The underlying
product evaluation, including its base triangle, is computed in
`ConstantFamilyEvaluation`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ConstantFamilyUniversalProperty
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M using (mapPost; mapPost-isEquiv)
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductSquares 𝒯 P using (module SecondFactor)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.EvaluatedPrecomposition 𝒯 M ℱ P using (module Precompose)
open import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.ConstantFamilyInternalFunctors 𝒯 M ℱ P using (module ConstantFamily)

module UniversalProperty (D : CAT) {E Γ : CAT} (q : MAP E Γ) where
  private
    module Constant = ConstantFamily D q using (category; projection; module At)
  category = Constant.category
  projection = Constant.projection

  module At {K : CAT} (k : MAP K Γ) where
    private
      module Product = Constant.At k using (functor; functor-isEquiv)
    source = FunOver k projection
    source-structure : MAP (Pullback k (pr₂ {D} {Γ})) Γ
    source-structure = k ∘ pullback₁
    target = FunOver source-structure q

    swap-over : FunctorOver (k ∘ pr₂ {C = D}) (k ∘ pr₁ {D = D})
    swap-over = record { lift = swap
      ; comparison = (k ◁ pair-β₁ pr₂ pr₁) ∙ comp-assoc swap pr₁ k }
    private
      module Swapped = Precompose q swap-over using (functor; module Equivalence)
    swap-isEquivalence : IsEquiv Swapped.functor
    swap-isEquivalence = Swapped.Equivalence.functor-isEquiv (swap-isEquiv D K)

    private
      module Domain = SecondFactor D k using (square; square-isPullback)
    inclusion : FunctorOver (k ∘ pr₂ {C = D}) source-structure
    inclusion = record { lift = pullbackLift Domain.square
      ; comparison = (k ◁ ConeIso.leftIso (pullbackLift-β Domain.square)) ∙
          comp-assoc (pullbackLift Domain.square) pullback₁ k }
    private
      module Restricted = Precompose q inclusion using (functor; module Equivalence)
    restriction-isEquiv : IsEquiv Restricted.functor
    restriction-isEquiv = Restricted.Equivalence.functor-isEquiv Domain.square-isPullback

    functor : MAP source target
    functor = IsEquiv.inverse restriction-isEquiv ∘ (Swapped.functor ∘ Product.functor)
    abstract
      functor-isEquiv : IsEquiv functor
      functor-isEquiv = equiv-compose _ _
        (equiv-compose _ _ Product.functor-isEquiv swap-isEquivalence)
        (equiv-inverse restriction-isEquiv)
    maps : MAP (MapOver k projection) (MapOver source-structure q)
    maps = mapPost functor
    maps-isEquiv : IsEquiv maps
    maps-isEquiv = mapPost-isEquiv functor functor-isEquiv
```
