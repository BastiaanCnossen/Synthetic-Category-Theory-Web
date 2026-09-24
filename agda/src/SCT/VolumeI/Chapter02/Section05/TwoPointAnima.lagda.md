# The two-point anima

The interval-core clause supplies the equivalence with an anima.
Recognition and invariance of groupoids under equivalence then give
the primitive anima witness, without assuming general coproduct closure.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section01.IntervalCore as Interval
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition

module SCT.VolumeI.Chapter02.Section05.TwoPointAnima
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (A : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R)
  (B : Coproducts.CoproductStructure 𝒯 M)
  (K : Interval.IntervalCoreAxiom 𝒯 M B I) where

open Recognition 𝒯 M ℱ P I E R
open Consequences A
open Coproducts.CoproductStructure B
open Interval 𝒯 M B I using (intervalCore)
open Interval.IntervalCoreAxiom K
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (core-isAn)

two-point-isAn : isAn (One ⊔ One)
two-point-isAn = equivalence-reflects-anima intervalCore intervalCore-isEquiv (core-isAn [1])

two-point-isGroupoid : IsGroupoid (One ⊔ One)
two-point-isGroupoid = anima-isGroupoid two-point-isAn
```
