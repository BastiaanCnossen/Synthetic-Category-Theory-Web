# Hom categories are groupoids

For `cor:Hom_Groupoids_Are_Groupoids`, identify the fiber of a slice
projection with the category of arrows having both specified endpoints.
The slice projection is a right fibration, so its fibers are groupoids.
The comparison here is derived from ordinary pullback pasting.

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
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionFibers as Fibers

module SCT.VolumeI.Chapter04.Section03.HomGroupoids
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section03.SliceFibrations 𝒯 M ℱ P I E S Q
open import SCT.VolumeI.Chapter04.Section02.FiberGroupoids 𝒯 M ℱ P I E R
  using (right-fiber-isGroupoid)
open import SCT.VolumeI.Chapter02.Section04.BasicClosure 𝒯 M ℱ P I E R
  using (IsGroupoid; equivalence-preserves-groupoid)

module SliceFiber {C : CAT} (x y : Obj-abs C) where
  boundary : (pair (id C) (const y) ∘ x) =₁ pair x y
  boundary = pair-cong (comp-unitˡ x) (const-One y ∙ const-pre y x) ∙
    pair-pre (id C) (const y) x

  module FiberComparison = Fibers.Fiber 𝒯 P endpoints (pair (id C) (const y)) x (pair x y) boundary
    using (fiber-to-target; fiber-to-target-isEquiv)
  open FiberComparison public

abstract
  hom-isGroupoid : {C : CAT} (x y : Obj-abs C) → IsGroupoid (Hom C x y)
  hom-isGroupoid x y = equivalence-preserves-groupoid
    (SliceFiber.fiber-to-target x y) (SliceFiber.fiber-to-target-isEquiv x y)
    (right-fiber-isGroupoid (slice-projection y) (slice-isRightFibration y) x)
```
