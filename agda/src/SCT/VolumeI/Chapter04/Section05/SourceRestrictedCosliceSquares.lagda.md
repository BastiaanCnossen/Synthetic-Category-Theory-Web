# The canonical coslice square of the source-restricted lift

The source-restricted lifting functor is a left adjoint section.
Its usual induced coslice functor therefore gives a pullback square,
with the inverse unit component as the specified source comparison.
The first square is between iterated coslices. The final construction
flattens both coslices while retaining its transported vertical map and
matching. Identifying that map with the image functor remains a separate
comparison.

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
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section05.SourceRestrictedCosliceSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter04.Section05.SourceRestrictedLifts as Restriction
import SCT.VolumeI.Chapter04.Section04.AdjointSectionCosliceSquares as SquaresOfSections
import SCT.VolumeI.Chapter04.Section03.IteratedCoslicePrecomposition as Flattening
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackReindexing as Reindexing
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)

module Covariant {C D : CAT} (p : MAP C D) (w : Fibration.CocartesianFibration p)
  (x : Obj-abs C) (β : Obj-abs (Coslice D (p ∘ x))) where
  private
    module Fixed = Restriction.Covariant 𝒯 M ℱ P I E S Q R p w x
      using (evaluation; section; value; evaluation-comparison; original-section)
    module Result = SquaresOfSections.FromSection 𝒯 M ℱ P I E S Q R Fixed.value β
      using (source-comparison; functor; square; comparison; square-isPullback)

  evaluation = Fixed.evaluation
  lift-object = Fixed.section ∘ β
  open Fixed public using (evaluation-comparison; original-section)
  open Result public using (source-comparison; functor; square; comparison; square-isPullback)

  module Flattened where
    private
      module Upstairs = Flattening.At 𝒯 M ℱ P I E S Q x lift-object
        using (functor; isEquiv; precompose; projection)
      module Downstairs = Flattening.At 𝒯 M ℱ P I E S Q (p ∘ x) β
        using (functor; isEquiv; precompose; projection)
      module Reindexed = Reindexing.Along 𝒯 P Result.square Result.square-isPullback
        Downstairs.precompose Downstairs.functor Downstairs.isEquiv Downstairs.projection
        Upstairs.precompose Upstairs.functor Upstairs.isEquiv Upstairs.projection
        using (square; square-isPullback; computation; cospan; restricted)

    precompose = Upstairs.precompose
    base-precompose = Downstairs.precompose
    target-object = coslice-projection x ∘ lift-object
    flattened-square = coneSwap Reindexed.square

    abstract
      flattened-square-isPullback : IsPullback flattened-square
      flattened-square-isPullback = pullback-swap Reindexed.square Reindexed.square-isPullback

    open Reindexed public using (computation; cospan; restricted)
```
