# The coslice pullback of a chosen lift

Restrict the lifting adjunction to a source, take its coslice pullback,
and flatten both iterated coslices. The resulting square has the two
precomposition functors as its horizontal sides. Its vertical map into
the base coslice still includes adjunction transposition and its unit;
it is retained explicitly for comparison with the usual induced functor.
No identification with the prescribed hom square is asserted here.

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

module SCT.VolumeI.Chapter04.Section05.LiftCosliceSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
import SCT.VolumeI.Chapter04.Section05.SourceRestrictedLifts as Restriction
import SCT.VolumeI.Chapter04.Section03.IteratedCoslicePrecomposition as Flattening
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackReindexing as Reindexing

module Covariant {C D : CAT} (p : MAP C D) (w : Fibration.CocartesianFibration p)
  (x : Obj-abs C) (β : Obj-abs (Coslice D (p ∘ x))) where
  private
    module Fixed = Restriction.Covariant 𝒯 M ℱ P I E S Q R p w x
      using (evaluation; evaluation-comparison; original-section; module At)
    module Lift = Fixed.At β using (lift-object; module Pullback)
    module Upstairs = Flattening.At 𝒯 M ℱ P I E S Q x Lift.lift-object
      using (functor; isEquiv; precompose; projection)
    module Downstairs = Flattening.At 𝒯 M ℱ P I E S Q (p ∘ x) β
      using (functor; isEquiv; precompose; projection)
    module Reindexed = Reindexing.Along 𝒯 P Lift.Pullback.square Lift.Pullback.square-isPullback
      Downstairs.precompose Downstairs.functor Downstairs.isEquiv Downstairs.projection
      Upstairs.precompose Upstairs.functor Upstairs.isEquiv Upstairs.projection
      using (square; square-isPullback; computation; cospan; restricted)

  lift-object = Lift.lift-object
  evaluation = Fixed.evaluation
  precompose = Upstairs.precompose
  base-precompose = Downstairs.precompose
  target-object = coslice-projection x ∘ lift-object

  square : Cone evaluation base-precompose (Coslice C target-object)
  square = coneSwap Reindexed.square

  abstract
    square-isPullback : IsPullback square
    square-isPullback = pullback-swap Reindexed.square Reindexed.square-isPullback

  open Fixed public using (evaluation-comparison; original-section)
  open Reindexed public using (cospan; restricted; computation)
```
