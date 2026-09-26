# Mapping into a pullback over the base

A functor from `X → C` to `D ×_S C → C` is equivalently a functor
from `X → C → S` to `D → S`. Apply the functor category to the
pullback defining `D ×_S C`, take the fiber at `X → C`, and paste the
two pullback squares. This supplies both the functor-category and
mapping-anima comparisons used for relative internal functor categories.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTargets
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Categories.FunctorCategories ℱ using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P
  using (mappedCone; fun-preserves-pullback)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange 𝒯 M ℱ using (post-nameFun)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P

module PullbackTarget {X C D S : CAT} (f : MAP C S) (g : MAP D S) (r : MAP X C) where
  target = Pullback g f
  projection : MAP target C
  projection = pullback₂

  right : Cone (funPost {C = X} f) (funPost {C = X} g) (Fun X target)
  right = mappedCone X (coneSwap (pullbackCone g f))

  right-isPullback : IsPullback right
  right-isPullback = fun-preserves-pullback X (coneSwap (pullbackCone g f))
    (pullback-swap (pullbackCone g f) (pullbackCone-isPullback g f))

  inner : Cone (nameFun r) (funPost projection) (FunOver r projection)
  inner = coneSwap (pullbackCone (funPost projection) (nameFun r))

  inner-isPullback : IsPullback inner
  inner-isPullback = pullback-swap (pullbackCone (funPost projection) (nameFun r))
    (pullbackCone-isPullback (funPost projection) (nameFun r))

  pasted = PasteCones.flatten (nameFun r) (funPost f) right inner

  pasted-isPullback : IsPullback pasted
  pasted-isPullback = Pasting.paste-isPullback (nameFun r) (funPost f) (funPost g)
    right right-isPullback inner inner-isPullback

  outer : Cone (funPost g) (nameFun (f ∘ r)) (FunOver r projection)
  outer = coneSwap (changeLeft (post-nameFun f r) pasted)

  outer-isPullback : IsPullback outer
  outer-isPullback = pullback-swap (changeLeft (post-nameFun f r) pasted)
    (ChangeLeft.preserve (post-nameFun f r) (funPost g) pasted pasted-isPullback)

  abstract
    functor : MAP (FunOver r projection) (FunOver (f ∘ r) g)
    functor = pullbackLift outer

    functor-isEquiv : IsEquiv functor
    functor-isEquiv = outer-isPullback

    comparison : ConeIso (conePre functor (pullbackCone (funPost g) (nameFun (f ∘ r)))) outer
    comparison = pullbackLift-β outer

    forget-comparison : (Over.forget (f ∘ r) g ∘ functor) =₁
      (funPost (pullback₁ {f = g} {f}) ∘ Over.forget r projection)
    forget-comparison = ConeIso.leftIso comparison

  maps : MAP (MapOver r projection) (MapOver (f ∘ r) g)
  maps = mapPost functor

  maps-isEquiv : IsEquiv maps
  maps-isEquiv = mapPost-isEquiv functor functor-isEquiv
```

The cone comparison retains the specified pullback identification.
Its upper leg is postcomposition with the first projection, as shown
by `forget-comparison`.
