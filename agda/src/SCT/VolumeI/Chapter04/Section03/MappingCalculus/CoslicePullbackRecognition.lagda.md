# Recognizing a coslice pullback from its arrow family

If the endpoint-fiber introduction of the image of a universal arrow
is an equivalence, the square of the actual induced coslice functor is a
pullback. Its matching is the target component of the complete arrow
comparison used to identify this functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CoslicePullbackRecognition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberExpressions 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I using (Coslice; coslice-projection)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneIso-swap; coneSwap-pre)
import SCT.VolumeI.Chapter04.Section03.CosliceFunctors as Functors
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceImageExpressions as Images
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressionCones as Cones
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.RelativeCosliceIntroductions as Introductions
open Laws.PullbackStructure P using (pullbackCone)

module At {C D : CAT} (p : MAP C D) (x : Obj-abs C) (b : Obj-abs D)
  (α : (p ∘ x) =₁ b) where
  private
    module Actual = Functors.At 𝒯 M ℱ P I p x b α using (functor)
    module Image = Images.At 𝒯 M ℱ P I p x b α
      using (image-expression; projection; expression-computation)
    module Introduction = Introductions.At 𝒯 M ℱ P I p b (coslice-projection x) Image.image-expression
      using (relative-expression; outer; ordinary; factor-cone; comparison; module Pullback)
    module Full = Cones.At.Along 𝒯 M ℱ P I b Actual.functor (p ∘ coslice-projection x)
      Image.image-expression Image.projection Image.expression-computation using (comparison)
    module H = EndpointFiber (const {P = C} b) p

  functor = Actual.functor
  image-expression = Image.image-expression
  introduction = H.lift (coslice-projection x) Introduction.relative-expression

  comparison : ConeIso
    (conePre functor (coneSwap (pullbackCone endpoints (pair (const b) (id D)))))
    Introduction.factor-cone
  comparison = coneIso-compose (coneIso-inverse Introduction.comparison)
    (coneIso-compose (coneIso-swap Full.comparison)
      (coneSwap-pre functor (pullbackCone endpoints (pair (const b) (id D)))))

  square : Cone (coslice-projection b) p (Coslice C x)
  square = record { left = functor ; right = coslice-projection x ; match = ConeIso.leftIso comparison }

  module Recognized (e : IsEquiv introduction) where
    private
      module Result = Introduction.Pullback.WithFunctor e functor comparison using (square-isPullback)
    abstract
      square-isPullback : IsPullback square
      square-isPullback = Result.square-isPullback
```
