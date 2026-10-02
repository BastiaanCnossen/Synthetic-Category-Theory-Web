# The morphisms of a subcategory are closed under composition

For `ex:Morphisms_In_Subcategory`, lift the two short edges of the ambient
composite triangle. The subcategory inclusion is an embedding, so the
specified middle matching lifts too. The lifted triangle supplies the
required composite. Identities follow from functoriality.

The collection of morphisms of a subcategory is the morphism image of the
embedding itself, via identity factorizations. The argument is therefore
the closure of embedding images in `EmbeddingImageClosure`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.Section01.SubcategoryClosure
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section03.FactorizationCalculus
  vocabulary terminal products productLaws composition
  using (lift-id)
open import SCT.VolumeI.Chapter03.Section01.Subcategories 𝒯 M P I
  using (IsSubcategory; subcategory-isEmbedding)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I
  using (subcategoryMorphisms)
open import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.CompositionClosure 𝒯 M ℱ P I E S
  using (ClosedUnderComposition)
open import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.EmbeddingImageClosure 𝒯 M ℱ P I E S
  using () renaming (module Closure to ImageClosure)

module Closure {A C : CAT} (f : MAP A C) (sub : IsSubcategory f) where
  W = subcategoryMorphisms f sub
  module Image = ImageClosure f (subcategory-isEmbedding f sub) W
    (lift-id (mapPost f)) (lift-id (mapPost f))

  closed : ClosedUnderComposition W
  closed = Image.closed

subcategory-morphisms-closed : {A C : CAT} (f : MAP A C) (sub : IsSubcategory f) →
  ClosedUnderComposition (subcategoryMorphisms f sub)
subcategory-morphisms-closed = Closure.closed
```
