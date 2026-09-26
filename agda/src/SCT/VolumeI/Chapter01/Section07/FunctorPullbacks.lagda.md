# Functor categories preserve pullbacks

For `lem:Functor_Category_Preserves_Pullbacks`, apply mapping-anima
detection to the specified functor-category square. The test in
`PullbackMappingTests` identifies its whole cone with the mapping-anima
pullback at the product parameter. Its comparisons retain the original
commutativity identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.FunctorPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M)
  (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯 M ℱ
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks 𝒯 M P using (map-detects-pullback)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.PullbackMappingTests 𝒯 M ℱ P using (module MappingTest)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.MappedCones 𝒯 M ℱ P public

fun-preserves-pullback : {C D E S : CAT} {f : MAP C E} {g : MAP D E}
  (T : CAT) (s : Cone f g S) → IsPullback s → IsPullback (mappedCone T s)
fun-preserves-pullback T s es = map-detects-pullback (mappedCone T s)
  (λ X → MappingTest.square-isPullback X T s es)

module FunctorPullback {C D E : CAT} (T : CAT) (f : MAP C E) (g : MAP D E) where
  S = Fun T (Pullback f g)
  F = funPost {C = T} f
  G = funPost {C = T} g
  R = Pullback F G

  original : Cone f g (Pullback f g)
  original = pullbackCone f g

  square : Cone F G S
  square = mappedCone T original

  comparison : MAP S R
  comparison = pullbackLift square

  comparison-computation : ConeIso (conePre comparison (pullbackCone F G)) square
  comparison-computation = pullbackLift-β square

  square-isPullback : IsPullback square
  square-isPullback = fun-preserves-pullback T original (pullbackCone-isPullback f g)

  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = square-isPullback
```
