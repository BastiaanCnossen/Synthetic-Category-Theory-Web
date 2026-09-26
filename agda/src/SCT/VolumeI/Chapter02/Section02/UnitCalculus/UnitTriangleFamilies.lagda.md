# The two degenerate triangle families

Apply universal evaluation to the interval's two degenerate triangles.
The three comparisons in each module are separate endpoint claims for
these actual families on `Ar C`. They compare restriction cones, whose
endpoint diagrams lie in `Fun One C`. Each `Evaluated` submodule also
provides the three converted endpoint equations in `C`, with the same
edge comparisons and the specified endpoint frames.

`TriangleFamilyPresentations` recognizes the evaluated long edges as
composites with their specified frames. `DirectUnitPresentations` gives
the unit comparisons for the original universal arrow and identity
expressions, using the direct degeneracy construction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.UnitCalculus.UnitTriangleFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleFamilies 𝒯 M ℱ P I E public
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EvaluatedTriangleFamilies as EvaluatedFamilies
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.IdentityComposites 𝒯 M ℱ P I E
  using (interval-left-unit; interval-right-unit)

module LeftUnit (C : CAT) where
  open UniversalWitness interval-left-unit C public
  module Evaluated = EvaluatedFamilies.Family.Witness 𝒯 M ℱ P I E witness

module RightUnit (C : CAT) where
  open UniversalWitness interval-right-unit C public
  module Evaluated = EvaluatedFamilies.Family.Witness 𝒯 M ℱ P I E witness
```
