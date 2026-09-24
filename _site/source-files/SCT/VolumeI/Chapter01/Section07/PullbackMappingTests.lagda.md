# The mapping-anima test for a functor-category pullback

Uncurrying identifies the four corners and the specified square before
any pullback hypothesis is used. The square at the product parameter is
a pullback by mapping-anima preservation. Transfer its universal property
along the whole-cone comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section07.PullbackMappingTests
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M F
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks 𝒯 M P
  using (map-preserves-pullback)
open import SCT.VolumeI.Chapter01.Section06.ConeTransportPullbacks 𝒯 P using (module Transfer)
open import SCT.VolumeI.Chapter01.Section07.UncurryingSquares 𝒯 M F P using (module SquareComparison)

module MappingTest {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (T K : CAT) (original : Cone f g S) (original-isPullback : IsPullback original) where

  open SquareComparison T K original public

  mapping-isPullback : IsPullback mappingSquare
  mapping-isPullback = map-preserves-pullback (T × K) original original-isPullback

  module Transferred = Transfer testedSquare mappingSquare U.forward U.forward-isEquiv
    forward forward-iso forward-reflect comparison mapping-isPullback

  square-isPullback : IsPullback testedSquare
  square-isPullback = Transferred.source-isPullback (map-isAn T (Fun K S))
    (pullback-isAn _ _ (map-isAn T (Fun K C))
      (map-isAn T (Fun K D)) (map-isAn T (Fun K E)))
```
