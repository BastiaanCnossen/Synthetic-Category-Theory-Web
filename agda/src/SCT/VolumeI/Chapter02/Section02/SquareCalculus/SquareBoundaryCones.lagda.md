# The six endpoint cones of the two square triangles

Each comparison retains the boundary restriction on both edges. The
source is expressed using the square's canonical vertex frames; the
target is the corresponding endpoint cone of a restricted triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareFaceCorners as Faces
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.FramedRestrictionCorners as Corners

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareBoundaryCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareShape 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates 𝒯 M ℱ using (coinsert)
module Shape = Faces 𝒯 M ℱ P I E
  using (module LowerMiddleForward; module LowerSource; module LowerTargetBack; module UpperMiddle; module UpperSource; module UpperTargetBack)
module Corner = Corners 𝒯 M ℱ P

module At {Γ C : CAT} (W : MAP Γ (Fun ([1] × [1]) C)) where
  module UpperMiddle = Corner.At one zero d₂ d₀ j₀ (face-middle ⁻¹)
    (coinsert zero) (insert one) Shape.UpperMiddle.Face.Source.first Shape.UpperMiddle.Face.Target.first
    Shape.UpperMiddle.Face.Source.second Shape.UpperMiddle.Face.Target.second Shape.UpperMiddle.corner W

  module LowerMiddle = Corner.At one zero d₂ d₀ j₁ (face-middle ⁻¹)
    (insert zero) (coinsert one) Shape.LowerMiddleForward.Face.Source.first Shape.LowerMiddleForward.Face.Target.first
    Shape.LowerMiddleForward.Face.Source.second Shape.LowerMiddleForward.Face.Target.second Shape.LowerMiddleForward.corner W

  module UpperSource = Corner.At zero zero d₁ d₂ j₀ face-bottom
    diagonal (coinsert zero) Shape.UpperSource.Face.Source.first Shape.UpperSource.Face.Target.first
    Shape.UpperSource.Face.Source.second Shape.UpperSource.Face.Target.second Shape.UpperSource.corner W

  module LowerSource = Corner.At zero zero d₁ d₂ j₁ face-bottom
    diagonal (insert zero) Shape.LowerSource.Face.Source.first Shape.LowerSource.Face.Target.first
    Shape.LowerSource.Face.Source.second Shape.LowerSource.Face.Target.second Shape.LowerSource.corner W

  module UpperTarget = Corner.At one one d₁ d₀ j₀ (face-top ⁻¹)
    diagonal (insert one) Shape.UpperTargetBack.Face.Source.first Shape.UpperTargetBack.Face.Target.first
    Shape.UpperTargetBack.Face.Source.second Shape.UpperTargetBack.Face.Target.second Shape.UpperTargetBack.corner W

  module LowerTarget = Corner.At one one d₁ d₀ j₁ (face-top ⁻¹)
    diagonal (coinsert one) Shape.LowerTargetBack.Face.Source.first Shape.LowerTargetBack.Face.Target.first
    Shape.LowerTargetBack.Face.Source.second Shape.LowerTargetBack.Face.Target.second Shape.LowerTargetBack.corner W

```
