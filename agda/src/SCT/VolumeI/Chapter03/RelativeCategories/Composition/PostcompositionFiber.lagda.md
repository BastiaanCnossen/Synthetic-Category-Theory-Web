# Fibers of relative postcomposition

The fiber of postcomposition over a specified functor to the target is
the functor category over that target. Paste the cartesian forgetful
square with the named functor's fiber. This keeps the original relative
triangle while changing the base from S to D.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionFiber
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullbackCone-isPullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionCartesian 𝒯 M ℱ P using (module Postcomposition)

module At {K C D S : CAT} {f : MAP C S} {g : MAP D S}
  (k : MAP K D) (u : FunctorOver f g) (t : MAP K S)
  (point : Obj-abs (FunOver t g))
  (point-comparison : (Over.forget t g ∘ point) =₁ nameFun k) where
  module Post = Postcompose t u using (functor)
  module Cartesian = Postcomposition t u using (square; square-isPullback)
  category = Pullback Post.functor point
  inner = coneSwap (pullbackCone Post.functor point)
  right = coneSwap Cartesian.square
  module Paste = PasteCones point (Over.forget t g) right using (flatten)
  pasted = Paste.flatten inner
  outer = coneSwap (changeLeft point-comparison pasted)
  abstract
    pasted-isPullback : IsPullback pasted
    pasted-isPullback = Pasting.paste-isPullback point (Over.forget t g)
      (funPost (FunctorLift.lift u)) right (pullback-swap Cartesian.square Cartesian.square-isPullback)
      inner (pullback-swap (pullbackCone Post.functor point) (pullbackCone-isPullback Post.functor point))
    outer-isPullback : IsPullback outer
    outer-isPullback = pullback-swap (changeLeft point-comparison pasted)
      (ChangeLeft.preserve point-comparison (funPost (FunctorLift.lift u)) pasted pasted-isPullback)
  functor : MAP category (FunOver k (FunctorLift.lift u))
  functor = pullbackLift outer
  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = outer-isPullback
    comparison : ConeIso (conePre functor (pullbackCone (funPost (FunctorLift.lift u)) (nameFun k))) outer
    comparison = pullbackLift-β outer
    forget-comparison : (Over.forget k (FunctorLift.lift u) ∘ functor) =₁
      (Over.forget t f ∘ pullback₁ {f = Post.functor} {point})
    forget-comparison = ConeIso.leftIso comparison

module Fiber {K C D S : CAT} {f : MAP C S} {g : MAP D S}
  (k : MAP K D) (u : FunctorOver f g) where
  t = g ∘ k
  point-over : FunctorOver t g
  point-over = record { lift = k ; comparison = idIso t }
  module Point = Over.Name t g point-over using (object; comparison)
  open At k u t Point.object (ConeIso.leftIso Point.comparison) public
```
