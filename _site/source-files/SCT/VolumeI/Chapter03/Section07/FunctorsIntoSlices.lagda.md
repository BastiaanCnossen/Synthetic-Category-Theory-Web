# Functors into slices as functors out of joins

For `lem:Functor_Categories_Into_Slices`, the tested slice pullback has
a lower map that factors through the variable functor and the fixed
functor `ψ`. The mapping-out square for the join is the pullback along
the second factor. The nesting equivalence therefore gives the desired
square. Its lower-left projection is the actual postcomposition by the
slice projection, and its right-hand map restricts to the two join
inclusions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to zeroℕ)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Axiom

module SCT.VolumeI.Chapter03.Section07.FunctorsIntoSlices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ hiding (_⋆_)
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; IsPullback; conePre; pullback-η; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneRetarget; coneRetarget-β)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.Pasting.UniversalNestedPullbacks 𝒯 P using (module Nested)
open import SCT.VolumeI.Chapter03.Section06.Joins 𝒯 M ℱ B P U I J using (_⋆_)
open import SCT.VolumeI.Chapter03.Section06.JoinMappingOut 𝒯 M ℱ B P U I J using (module MappingOut)
open import SCT.VolumeI.Chapter03.Section07.MappingCalculus.SliceFunctorPullback 𝒯 M ℱ P I using (module Tested)
open import SCT.VolumeI.Chapter03.Section07.Slices 𝒯 M ℱ P I using (module Slice)

module SliceComparison (X : CAT) {Y C : CAT} (ψ : MAP Y C) where
  module Slice′ = Slice ψ using (category; projection)
  module Join = MappingOut X Y C using (cone; isPullback; restriction; cylinder-endpoints; boundary-projections)
  module Test = Tested X ψ using (cone; isPullback; fixed; projection; diagram)
  Source = Fun X Slice′.category
  inner = coneSwap Join.cone
  outer = coneSwap Test.cone
  abstract
    inner-isPullback : IsPullback inner
    inner-isPullback = pullback-swap Join.cone Join.isPullback
    outer-isPullback : IsPullback outer
    outer-isPullback = pullback-swap Test.cone Test.isPullback
  module Nested′ = Nested Test.fixed Join.boundary-projections Join.cylinder-endpoints inner inner-isPullback
    using (N; insert; insert-isEquiv; insertionCone; outerLeft)
  abstract
    factor : MAP Source Nested′.N
    factor = Nested′.insert ∘ pullbackLift outer
    factor-isEquiv : IsEquiv factor
    factor-isEquiv = equiv-compose (pullbackLift outer) Nested′.insert outer-isPullback Nested′.insert-isEquiv
    projection-comparison : (pullback₁ ∘ factor) =₁ Test.projection
    projection-comparison = pullbackLift-β₁ outer ∙
      ((pullbackLift-β₁ Nested′.insertionCone ▷ pullbackLift outer) ∙
        (comp-assoc (pullbackLift outer) Nested′.insert pullback₁) ⁻¹)
  functor : MAP Source (Fun (X ⋆ Y) C)
  functor = pullback₂ ∘ factor
  original = conePre factor (pullbackCone Test.fixed Join.restriction)
  before-swap : Cone Test.fixed Join.restriction Source
  before-swap = coneRetarget original Test.projection functor projection-comparison (idIso functor)
  cone : Cone Join.restriction Test.fixed Source
  cone = coneSwap before-swap
  abstract
    before-swap-isPullback : IsPullback before-swap
    before-swap-isPullback = pullback-cone-invariant
      (coneRetarget-β original Test.projection functor projection-comparison (idIso functor))
      (equiv-transport ((pullback-η factor) ⁻¹) factor-isEquiv)
    isPullback : IsPullback cone
    isPullback = pullback-swap before-swap before-swap-isPullback
```
