# The Segal axiom

The specified restriction functor sends a triangle to its two short edges,
including their middle-vertex identification. `axiom:B_Segal_Axiom`
says that this functor is an equivalence. The axiom below adds exactly
this assertion to the structure used in Section 2.1.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.SegalAxiom
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.TrianglesAndComposites 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)

record SegalAxiom : Set (c ⊔ m) where
  field
    segal-isEquiv : (C : CAT) → IsEquiv (composable-restriction C)

  segal-isPullback : (C : CAT) → IsPullback (triangle-cone C)
  segal-isPullback = segal-isEquiv
```
