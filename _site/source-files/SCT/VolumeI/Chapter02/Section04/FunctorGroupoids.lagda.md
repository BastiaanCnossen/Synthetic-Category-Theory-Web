# Functor categories with groupoid targets

For `lem:Functor_Category_Into_Groupoid_Is_Groupoid`, the exponential law
identifies constant arrows in `Fun C X` with postcomposition by constant
arrows in `X`, after exchanging the two diagram variables. The comparison
of the actual functors is proved in `ConstantExponential`.

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

module SCT.VolumeI.Chapter02.Section04.FunctorGroupoids
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R public
open import SCT.VolumeI.Chapter02.Section04.ConstantDiagrams.ConstantExponential 𝒯 M ℱ
  using (module Constant)

functor-isGroupoid : (C X : CAT) → IsGroupoid X → IsGroupoid (Fun C X)
functor-isGroupoid C X = Constant.preserves-equivalence [1] C X
```
