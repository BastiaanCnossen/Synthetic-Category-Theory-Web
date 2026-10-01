# Relative coslices as endpoint pullbacks

The relative coslice of `d` along `f` classifies arrows from the constant
object `d` to `f`. Pullback cancellation identifies its defining iterated
pullback with the single endpoint pullback. The comparison retains its
whole cone, including the specified identification over the target base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.RelativeCoslicePresentation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section03.RelativeSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullbackCone-isPullback)
import SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeSquares as BaseChange
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P using (FunctorOver)

module At {C D : CAT} (f : MAP C D) (d : Obj-abs D) where
  module Source = EndpointFiber (const {P = C} d) f
  module Target = RelativeCoslice f d
  private
    family-comparison : (pair (const d) (id D) ∘ f) =₁ pair (const d) f
    family-comparison = pair-cong (const-pre d f) (comp-unitˡ f) ∙
      pair-pre (const d) (id D) f
    module Change = BaseChange.Along 𝒯 P endpoints (pair (const d) (id D))
      (pullbackCone endpoints (pair (const d) (id D)))
      (pullbackCone-isPullback endpoints (pair (const d) (id D)))
      f family-comparison (pullbackCone endpoints (pair (const d) f))
      (pullbackCone-isPullback endpoints (pair (const d) f))
      using (square; square-isPullback; factor-cone; factor-computation)

  square : Cone (coslice-projection d) f Source.category
  square = Change.square

  coslice-cone = Change.factor-cone
  coslice-computation = Change.factor-computation

  square-isPullback : IsPullback square
  square-isPullback = Change.square-isPullback

  functor : MAP Source.category Target.category
  functor = pullbackLift square

  isEquiv : IsEquiv functor
  isEquiv = square-isPullback

  comparison : ConeIso (conePre functor (pullbackCone (coslice-projection d) f)) square
  comparison = pullbackLift-β square

  over-base : FunctorOver Source.base Target.projection
  over-base = record { lift = functor ; comparison = ConeIso.rightIso comparison }
```


