# Fibers of left and right fibrations are groupoids

For `cor:Fibers_Of_Left_Fibrations_Are_Groupoids`, pull back along an
absolute object of the base. The resulting left or right fibration has
terminal base, so its total category is a groupoid. The same argument
works for every specified pullback square over an absolute groupoid.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section02.FiberGroupoids
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section02.BaseChange 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter04.Section02.GroupoidBase 𝒯 M ℱ P I E R using (module OverGroupoid)
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
open import SCT.VolumeI.Chapter02.Section04.BasicClosure 𝒯 M ℱ P I E R using (terminal-isGroupoid)
open import SCT.VolumeI.Chapter01.Section06.Fibers 𝒯 P using (Fiber)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullbackCone-isPullback)

left-pullback-over-groupoid : {A B D X : CAT} {f : MAP A D} {v : MAP B D}
  (s : Cone f v X) → IsPullback s → IsGroupoid B →
  IsEquiv (Evaluation.directed-ev₀ f) → IsGroupoid X
left-pullback-over-groupoid s es eB ef = OverGroupoid.left-to-groupoid (Cone.right s) eB
  (left-base-change s es ef)

right-pullback-over-groupoid : {A B D X : CAT} {f : MAP A D} {v : MAP B D}
  (s : Cone f v X) → IsPullback s → IsGroupoid B →
  IsEquiv (Evaluation.directed-ev₁ f) → IsGroupoid X
right-pullback-over-groupoid s es eB ef = OverGroupoid.right-to-groupoid (Cone.right s) eB
  (right-base-change s es ef)

left-fiber-isGroupoid : {A B : CAT} (f : MAP A B) →
  IsEquiv (Evaluation.directed-ev₀ f) → (y : Obj-abs B) → IsGroupoid (Fiber f y)
left-fiber-isGroupoid f ef y = left-pullback-over-groupoid
  (pullbackCone f y) (pullbackCone-isPullback f y) terminal-isGroupoid ef

right-fiber-isGroupoid : {A B : CAT} (f : MAP A B) →
  IsEquiv (Evaluation.directed-ev₁ f) → (y : Obj-abs B) → IsGroupoid (Fiber f y)
right-fiber-isGroupoid f ef y = right-pullback-over-groupoid
  (pullbackCone f y) (pullbackCone-isPullback f y) terminal-isGroupoid ef
```
