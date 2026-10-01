# Hom categories as fibers of coslices

Pullback cancellation identifies the hom category with the fiber of the
coslice projection. The square includes its chosen map into the coslice
and its complete factorization computation. This step uses only the
endpoint pullbacks, without Segal, Rezk, or pointwise detection.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I public
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; conePre; IsPullback; pullbackCone-isPullback)
import SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeSquares as BaseChange

module At {C : CAT} (x z : Obj-abs C) where
  private
    family-comparison : (pair (const x) (id C) ∘ z) =₁ pair x z
    family-comparison = pair-cong (const-One x ∙ const-pre x z) (comp-unitˡ z) ∙
      pair-pre (const x) (id C) z
    module Change = BaseChange.Along 𝒯 P endpoints (pair (const x) (id C))
      (pullbackCone endpoints (pair (const x) (id C)))
      (pullbackCone-isPullback endpoints (pair (const x) (id C)))
      z family-comparison (pullbackCone endpoints (pair x z))
      (pullbackCone-isPullback endpoints (pair x z))
      using (square; square-isPullback; factor; factor-cone; factor-computation)

  square : Cone (coslice-projection x) z (Hom C x z)
  square = Change.square

  square-isPullback : IsPullback square
  square-isPullback = Change.square-isPullback

  inclusion : MAP (Hom C x z) (Coslice C x)
  inclusion = Change.factor

  endpoint-cone = Change.factor-cone
  endpoint-computation = Change.factor-computation

  comparison : MAP (Hom C x z) (Pullback (coslice-projection x) z)
  comparison = pullbackLift square

  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = square-isPullback

  comparison-computation : ConeIso
    (conePre comparison (pullbackCone (coslice-projection x) z)) square
  comparison-computation = pullbackLift-β square
```

An equivalence from a coslice over its target category induces an
equivalence from each hom category to the corresponding target fiber.
The proof transports the entire fiber square along the given triangle;
it makes no appeal to detecting equivalences objectwise.

```agda
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P using (FunctorOver)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks as Transport

module UnderEquivalence {C T : CAT} (x : Obj-abs C) (p : MAP T C)
  (f : FunctorOver (coslice-projection x) p) (ef : IsEquiv (FunctorLift.lift f))
  (z : Obj-abs C) where
  private
    module Source = At x z using (square; square-isPullback)
  cospan : CospanMap (coslice-projection x) z p z
  cospan = record
    { left = FunctorLift.lift f ; right = id One ; base = id C
    ; leftSquare = (comp-unitˡ (coslice-projection x)) ⁻¹ ∙ FunctorLift.comparison f
    ; rightSquare = (comp-unitˡ z) ⁻¹ ∙ comp-unitʳ z }

  square : Cone p z (Hom C x z)
  square = CospanMap.mapCone cospan Source.square

  private
    module Preserved = Transport.Mapped 𝒯 P cospan
      (degenerate-pullback (id-isEquiv C) (Transport.rightSquareOf 𝒯 P cospan)
        (id-isEquiv One)) Source.square Source.square-isPullback
      using (isPullback)

  square-isPullback : IsPullback square
  square-isPullback = Preserved.isPullback ef

  functor : MAP (Hom C x z) (Pullback p z)
  functor = pullbackLift square

  isEquiv : IsEquiv functor
  isEquiv = square-isPullback

  computation : ConeIso (conePre functor (pullbackCone p z)) square
  computation = pullbackLift-β square
```
