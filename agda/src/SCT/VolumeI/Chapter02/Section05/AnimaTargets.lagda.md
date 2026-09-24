# Mapping animae into anima targets

This proves `Map_is_Fun_for_groupoids` for the canonical inclusion.
Recognition makes `Fun C X` an anima when `X` is an anima. Its core
inclusion is therefore an equivalence; composing with the mapping-core
comparison gives precisely the displayed mapping inclusion.

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
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition

module SCT.VolumeI.Chapter02.Section05.AnimaTargets
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (A : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R) where

open Recognition 𝒯 M ℱ P I E R
open Consequences A
open import SCT.VolumeI.Chapter02.Section04.FunctorGroupoids 𝒯 M ℱ P I E R using (functor-isGroupoid)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (coreInclusion; core-of-anima)
import SCT.VolumeI.Chapter01.Section07.CoreOfFun as CoreOfFun
open import SCT.VolumeI.Chapter01.Section07.MappingComparison 𝒯 M ℱ using (mappingInclusion)

functor-isAn : (C X : CAT) → isAn X → isAn (Fun C X)
functor-isAn C X h = groupoid-isAn (functor-isGroupoid C X (anima-isGroupoid h))

mappingInclusion-isEquiv : (C X : CAT) → isAn X → IsEquiv (mappingInclusion C X)
mappingInclusion-isEquiv C X h = equiv-transport CoreComparison.inclusion-comparison
  (equiv-compose CoreComparison.comparison (coreInclusion (Fun C X)) CoreComparison.comparison-isEquiv
    (core-of-anima (Fun C X) (functor-isAn C X h)))
  where module CoreComparison = CoreOfFun.CoreOfFun 𝒯 M ℱ C X
```
