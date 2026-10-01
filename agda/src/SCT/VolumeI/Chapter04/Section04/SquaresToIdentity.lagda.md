# Squares into identity arrows

The adjunction between target evaluation and identity arrows identifies
squares from a fixed arrow to identity arrows with the coslice of its
target. This is an equivalence over the varying target category, with
both inverse comparisons over that category.

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

module SCT.VolumeI.Chapter04.Section04.SquaresToIdentity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.EvaluationAdjunctions 𝒯 M ℱ P I E S Q R
  using (target-evaluation-adjunction)
open import SCT.VolumeI.Chapter04.Section03.RelativeSlices 𝒯 M ℱ P I public
import SCT.VolumeI.Chapter04.Section04.CosliceAdjunctions as Coslices

module At {C : CAT} (u : Obj-abs (Ar C)) where
  module TargetSquares = RelativeCoslice (identityArrow {C}) u
  private
    module Transpose = Coslices.Absolute 𝒯 M ℱ P I E S Q
      (target-evaluation-adjunction C) u
      using (functor; isEquiv; equivalence; over-base; inverse-over-base;
        left-inverse-over-base; right-inverse-over-base)

  -- The forward functor fills the square from its target side.
  filling : MAP (Coslice C (ev₁ ∘ u)) TargetSquares.category
  filling = Transpose.functor

  filling-isEquiv : IsEquiv filling
  filling-isEquiv = Transpose.isEquiv

  open Transpose public using (equivalence; over-base; inverse-over-base;
    left-inverse-over-base; right-inverse-over-base)
```
