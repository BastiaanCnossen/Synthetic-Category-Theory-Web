# Comparing the coslice and hom pullback criteria

Pasting the coslice square with a hom-fiber square, then cancelling the
corresponding base hom-fiber square, gives the prescribed hom pullback.
The theorem below isolates the exact compatibility needed between the
two pasted rectangles. That compatibility remains an explicit hypothesis;
it is not inferred from agreement of the four vertex functors.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section05.CosliceHomCriterion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; ConeIso; IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange as ArrowChange
import SCT.VolumeI.Chapter01.Section06.PastingLemma as Pasting
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting as ConePasting
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceCompositionNaturality as CosliceSquares
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceFiberPrecomposition as FiberPrecomposition
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceFiberImages as FiberImages
import SCT.VolumeI.Chapter04.Section05.CocartesianMorphisms as Morphisms

module Along {C D : CAT} (F : MAP C D) {x y : Obj-abs C} (e : Obj-abs (Hom C x y)) where
  private
    module Coslice = CosliceSquares.Along 𝒯 M ℱ P I E S {C = C} {D = D} F {x = x} {y = y} e
      using (square; image-source; image-target; precompose; image-precompose)
    module HomSquare = Morphisms.Along 𝒯 M ℱ P I E S {C = C} {D = D} F {x = x} {y = y} e
      using (cocartesian-square; IsCocartesian)
  coslice-square = Coslice.square

  module AtTarget (z : Obj-abs C) where
    private
      module CPre = FiberPrecomposition.Along 𝒯 M ℱ P I E S {C = C} {x = x} {y = y} e z
        using (square; square-isPullback; hom-precompose; target-inclusion)
      module DPre = FiberPrecomposition.Along 𝒯 M ℱ P I E S
        {C = D} {x = F ∘ x} {y = F ∘ y} (hom-post F x y ∘ e) (F ∘ z)
        using (square; square-isPullback; target-inclusion)
      module XImage = FiberImages.At 𝒯 M ℱ P I F x z using (comparison)
      module YImage = FiberImages.At 𝒯 M ℱ P I F y z using (comparison)
      module First = ConePasting.PasteCones 𝒯 CPre.target-inclusion Coslice.image-source Coslice.square using (flatten)
      module Second = ConePasting.PasteCones 𝒯 (hom-post F x z) DPre.target-inclusion (coneSwap DPre.square) using (flatten)
      module Change = ArrowChange.ChangeLeft 𝒯 P XImage.comparison Coslice.image-precompose using (preserve)
      module Cancel = Pasting.Pasting 𝒯 P (hom-post F x z) DPre.target-inclusion Coslice.image-precompose
        (coneSwap DPre.square) (pullback-swap DPre.square DPre.square-isPullback) using (cancel-isPullback)

    coslice-rectangle = changeLeft XImage.comparison (First.flatten (coneSwap CPre.square))
    hom-rectangle = Second.flatten (HomSquare.cocartesian-square z)
    left-comparison = idIso CPre.hom-precompose
    right-comparison = YImage.comparison

    matching-compatibility : Set m
    matching-compatibility =
      (Cone.match hom-rectangle ∙ ((DPre.target-inclusion ∘ hom-post F x z) ◁ left-comparison)) =₂
      ((Coslice.image-precompose ◁ right-comparison) ∙ Cone.match coslice-rectangle)

    module Compatible (w : matching-compatibility) where
      rectangle-comparison : ConeIso coslice-rectangle hom-rectangle
      rectangle-comparison = record { leftIso = left-comparison ; rightIso = right-comparison ; compatible = w }

      module FromPullback (s : IsPullback coslice-square) where
        private
          module Paste = Pasting.Pasting 𝒯 P CPre.target-inclusion Coslice.image-source Coslice.image-precompose
            Coslice.square s using (paste-isPullback)
        abstract
          hom-square-isPullback : IsPullback (HomSquare.cocartesian-square z)
          hom-square-isPullback = Cancel.cancel-isPullback (HomSquare.cocartesian-square z)
            (pullback-cone-invariant rectangle-comparison
              (Change.preserve (First.flatten (coneSwap CPre.square))
                (Paste.paste-isPullback (coneSwap CPre.square) (pullback-swap CPre.square CPre.square-isPullback))))

  abstract
    from-compatible-coslice-square : IsPullback coslice-square →
      ((z : Obj-abs C) → AtTarget.matching-compatibility z) → HomSquare.IsCocartesian
    from-compatible-coslice-square s compatible z =
      AtTarget.Compatible.FromPullback.hom-square-isPullback z (compatible z) s
```
