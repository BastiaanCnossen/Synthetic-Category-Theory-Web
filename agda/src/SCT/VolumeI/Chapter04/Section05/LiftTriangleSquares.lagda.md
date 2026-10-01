# Pullback squares on triangles of a chosen lift

Apply the canonical coslice pullback of the source-restricted lifting
adjunction to the hom-fiber inclusions. The resulting pullback has literal
hom-precomposition along its two projections. Its other map is constructed
from the full coslice image cone. Identifying that map and its matching
with the prescribed hom-postcomposition square is a further obligation.

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

module SCT.VolumeI.Chapter04.Section05.LiftTriangleSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; ConeIso; conePre; IsPullback; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
import SCT.VolumeI.Chapter04.Section05.SourceRestrictedCosliceSquares as LiftSquares
import SCT.VolumeI.Chapter04.Section03.CosliceTriangleHomFibers as Triangles
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceImageFamilies as Images
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceFiberImages as FiberImages
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacksLeft as Projections

module Covariant {C D : CAT} (p : MAP C D) (w : Fibration.CocartesianFibration p)
  (x : Obj-abs C) (β : Obj-abs (Coslice D (p ∘ x))) (z : Obj-abs C) where
  private
    module Chosen = LiftSquares.Covariant 𝒯 M ℱ P I E S Q R p w x β
      using (evaluation; lift-object; functor; square; square-isPullback; source-comparison; evaluation-comparison)
    module Upstairs = Triangles.At 𝒯 M ℱ P I E S Q x Chosen.lift-object z
      using (y; hom-point; inclusion; precompose; square; square-isPullback)
    module Downstairs = Triangles.At 𝒯 M ℱ P I E S Q (p ∘ x) β (p ∘ z)
      using (y; hom-point; inclusion; precompose; square; square-isPullback)
    module Image = Images.At.Standard 𝒯 M ℱ P I p x using (comparison)
    module FiberImage = FiberImages.At 𝒯 M ℱ P I p x z using (comparison)
    evaluation-image : Chosen.evaluation =₁ Images.At.functor 𝒯 M ℱ P I p x
    evaluation-image = Image.comparison ∙ Chosen.evaluation-comparison
    projection = coslice-projection Chosen.lift-object
    base-projection = coslice-projection β

  target-object = Upstairs.y
  base-target = Downstairs.y
  hom-point = Upstairs.hom-point
  base-hom-point = Downstairs.hom-point
  hom-precompose = Upstairs.precompose
  base-hom-precompose = Downstairs.precompose
  hom-post-source = hom-post p x z

  cospan : CospanMap projection Upstairs.inclusion base-projection Downstairs.inclusion
  cospan = record
    { left = Chosen.functor ; right = hom-post-source ; base = Chosen.evaluation
    ; leftSquare = Cone.match Chosen.square
    ; rightSquare = (FiberImage.comparison ∙ (evaluation-image ▷ Upstairs.inclusion)) ⁻¹ }
  image-cone = CospanMap.mapCone cospan Upstairs.square
  private
    module Universal = UniversalCone Downstairs.square Downstairs.square-isPullback using (factor; factor-β)

  triangle-image : MAP (Hom C target-object z) (Hom D base-target (p ∘ z))
  triangle-image = Universal.factor image-cone
  image-computation : ConeIso (conePre triangle-image Downstairs.square) image-cone
  image-computation = Universal.factor-β image-cone
  private
    module Result = Projections.ProjectionSquare 𝒯 P cospan Chosen.square-isPullback
      Upstairs.square Upstairs.square-isPullback Downstairs.square Downstairs.square-isPullback
      triangle-image image-computation using (square; square-isPullback)

  square : Cone hom-post-source base-hom-precompose (Hom C target-object z)
  square = Result.square
  abstract
    square-isPullback : IsPullback square
    square-isPullback = Result.square-isPullback
  open Chosen public using (source-comparison)
```
