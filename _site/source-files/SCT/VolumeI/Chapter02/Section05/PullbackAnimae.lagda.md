# Pullbacks of animae and the core embedding

Recognition turns the groupoid pullback theorem into
`lem:Pullback_Of_Animae_Over_Category`. For
`prop:Groupoid_Core_Embeds_Into_C`, use the equivalent first-projection
criterion for an embedding. Both its source and target are animae, so
testing against animae suffices. The core universal property makes each
test the pullback of an equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition

module SCT.VolumeI.Chapter02.Section05.PullbackAnimae
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (A : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R) where

open Recognition 𝒯 M ℱ P I E R
open Consequences A
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter02.Section04.PullbackGroupoids 𝒯 M ℱ P I E S Q R
  using (pullback-isGroupoid)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M using (mapPost)
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (post-tests-animae)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks 𝒯 M P using (module MappingPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (pullback-equivalence)

pullback-of-animae : {X Y C : CAT} (f : MAP X C) (g : MAP Y C) →
  isAn X → isAn Y → isAn (Pullback f g)
pullback-of-animae f g ex ey = groupoid-isAn
  (pullback-isGroupoid f g (anima-isGroupoid ex) (anima-isGroupoid ey))

coreInclusion-isEmbedding : (C : CAT) → IsEmbedding (coreInclusion C)
coreInclusion-isEmbedding C = projection-embedding i
  (post-tests-animae (pullback-of-animae i i (core-isAn C) (core-isAn C)) (core-isAn C)
    pullback₁ (λ X xAn → tested X xAn))
  where
  i = coreInclusion C
  tested : (X : CAT) → isAn X → IsEquiv (mapPost {C = X} (pullback₁ {f = i} {i}))
  tested X xAn = equiv-transport (pullbackLift-β₁ Test.square)
    (equiv-compose Test.comparison pullback₁ Test.square-isPullback
      (pullback-equivalence (mapPost i) (mapPost i) (core-universal X C xAn)))
    where module Test = MappingPullback X i i
```
