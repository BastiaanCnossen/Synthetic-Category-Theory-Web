# General slice projections are fibrations

For `cor:General_Slice_Projections_Are_Fibrations`, the absolute general
slice of a diagram is a right fibration over the ambient category; the
coslice is a left fibration. Cylinder flattening compares the existing
Chapter 3 definitions with ordinary relative slices in a functor
category, retaining their projections.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CylinderEndpointComparison as Cylinder
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointProjectionFibrations as EndpointProjections
import SCT.VolumeI.Chapter03.Section07.Slices as General

module SCT.VolumeI.Chapter04.Section03.GeneralSliceFibrations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I
open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I
  using (module Evaluation)
open import SCT.VolumeI.Chapter04.Section02.Equivalences 𝒯 M ℱ P I using (module TotalEquivalence)
open import SCT.VolumeI.Chapter04.Section02.IsomorphismInvariance 𝒯 M ℱ P I
  using (left-invariance; right-invariance)
open General 𝒯 M ℱ P I using (constantFamily)

module Slice {Y C : CAT} (ψ : MAP Y C) where
  module Defined = General.Slice 𝒯 M ℱ P I ψ using (projection)
  module Compare = Cylinder.At 𝒯 M ℱ P I Y C (constantFamily Y C) (const (nameFun ψ))
    using (forward; forward-isEquiv; projection-comparison)
  module Known = EndpointProjections.Slice 𝒯 M ℱ P I E S Q (constantFamily Y C) (nameFun ψ)
    using (projection-isRightFibration)

  abstract
    projection-isRightFibration : IsEquiv (Evaluation.directed-ev₁ Defined.projection)
    projection-isRightFibration = TotalEquivalence.right-reflect Compare.forward Compare.forward-isEquiv
      Defined.projection (right-invariance (Compare.projection-comparison ⁻¹) Known.projection-isRightFibration)

module Coslice {Y C : CAT} (ψ : MAP Y C) where
  module Defined = General.Coslice 𝒯 M ℱ P I ψ using (projection)
  module Compare = Cylinder.At 𝒯 M ℱ P I Y C (const (nameFun ψ)) (constantFamily Y C)
    using (forward; forward-isEquiv; projection-comparison)
  module Known = EndpointProjections.Coslice 𝒯 M ℱ P I E S Q (constantFamily Y C) (nameFun ψ)
    using (projection-isLeftFibration)

  abstract
    projection-isLeftFibration : IsEquiv (Evaluation.directed-ev₀ Defined.projection)
    projection-isLeftFibration = TotalEquivalence.left-reflect Compare.forward Compare.forward-isEquiv
      Defined.projection (left-invariance (Compare.projection-comparison ⁻¹) Known.projection-isLeftFibration)
```
