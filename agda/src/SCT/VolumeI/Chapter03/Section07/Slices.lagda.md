# Absolute slice and coslice categories

For `cons:General_Slice_Category` in the absolute case, a slice object
is a constant family in `Fun Y C`, together with an arrow to the fixed
family `ψ`. We construct this directly from functor categories and a
pullback. The dual construction reverses the two endpoint conditions.

Both definitions retain the specified endpoint identification. The
relative construction over an arbitrary base, and the comparison with
mapping out of joins, are separate statements.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval

module SCT.VolumeI.Chapter03.Section07.Slices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Interval.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullbackCone-isPullback)
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P using (fun-preserves-pullback; mappedCone)

constantFamily : (Y C : CAT) → MAP C (Fun Y C)
constantFamily Y C = funCurry pr₁

endpoint : (Y : CAT) (e : Obj-abs [1]) → MAP Y ([1] × Y)
endpoint Y e = pair (const e) (id Y)

endpoints : (Y C : CAT) → MAP (Fun ([1] × Y) C) (Fun Y C × Fun Y C)
endpoints Y C = pair (funPre (endpoint Y zero)) (funPre (endpoint Y one))

module Slice {Y C : CAT} (ψ : MAP Y C) where
  boundary : MAP C (Fun Y C × Fun Y C)
  boundary = pair (constantFamily Y C) (const (nameFun ψ))

  category : CAT
  category = Pullback (endpoints Y C) boundary

  diagram : MAP category (Fun ([1] × Y) C)
  diagram = pullback₁

  projection : MAP category C
  projection = pullback₂

  matching : (endpoints Y C ∘ diagram) =₁ (boundary ∘ projection)
  matching = pullbackMatch

  cone : Cone (endpoints Y C) boundary category
  cone = pullbackCone (endpoints Y C) boundary

  universal : IsPullback cone
  universal = pullbackCone-isPullback (endpoints Y C) boundary

  functor-square-isPullback : (X : CAT) → IsPullback (mappedCone X cone)
  functor-square-isPullback X = fun-preserves-pullback X cone universal

module Coslice {X C : CAT} (φ : MAP X C) where
  boundary : MAP C (Fun X C × Fun X C)
  boundary = pair (const (nameFun φ)) (constantFamily X C)

  category : CAT
  category = Pullback (endpoints X C) boundary

  diagram : MAP category (Fun ([1] × X) C)
  diagram = pullback₁

  projection : MAP category C
  projection = pullback₂

  matching : (endpoints X C ∘ diagram) =₁ (boundary ∘ projection)
  matching = pullbackMatch

  cone : Cone (endpoints X C) boundary category
  cone = pullbackCone (endpoints X C) boundary

  universal : IsPullback cone
  universal = pullbackCone-isPullback (endpoints X C) boundary

  functor-square-isPullback : (Y : CAT) → IsPullback (mappedCone Y cone)
  functor-square-isPullback Y = fun-preserves-pullback Y cone universal
```
