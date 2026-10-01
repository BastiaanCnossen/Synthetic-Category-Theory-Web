# The lifting adjunction with source fixed

Base change along the source fiber restricts the chosen lifting
adjunction to a functor between coslices. The comparison with the
original lift and the section identification are retained. Thus later
arguments can use this adjunction without making new choices of lifts.

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

module SCT.VolumeI.Chapter04.Section05.SourceRestrictedLifts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SourceRestrictedEvaluation as Restriction
import SCT.VolumeI.Chapter04.Section04.AdjointSectionBaseChange as BaseChange
import SCT.VolumeI.Chapter04.Section04.CosliceAdjunctions as Coslices
import SCT.VolumeI.Chapter04.Section04.AdjunctionCosliceSquares as CosliceSquares

module Covariant {C D : CAT} (p : MAP C D) (w : Fibration.CocartesianFibration p)
  (x : Obj-abs C) where
  private
    module W = Fibration.CocartesianFibration w using (lift; left-adjoint-section)
    module Fixed = Restriction.At 𝒯 M ℱ P I p x
      using (inclusion; evaluation; square; square-isPullback; endpoint-computation; evaluation-comparison)
    module Changed = BaseChange.Left 𝒯 M ℱ P I E S Q R W.left-adjoint-section
      Fixed.inclusion Fixed.square Fixed.square-isPullback
      using (section; value; original-section; section-identification)
  open Fixed public using (inclusion; evaluation; square; square-isPullback; endpoint-computation; evaluation-comparison)
  open Changed public using (section; value; original-section; section-identification)

  private
    module Adj = LeftAdjointSection value using (adjunction)

  module At (β : Obj-abs (Coslice D (p ∘ x))) where
    lift-object : Obj-abs (Coslice C x)
    lift-object = section ∘ β

    module Universal = Coslices.Absolute 𝒯 M ℱ P I E S Q Adj.adjunction β
      using (functor; isEquiv; equivalence; over-base; inverse-over-base;
        left-inverse-over-base; right-inverse-over-base)

    module Pullback = CosliceSquares.At 𝒯 M ℱ P I E S Q Adj.adjunction β
      using (square; computation; square-isPullback; transposed; transposed-cone; transposed-computation; coslice-projection-computation)
```
