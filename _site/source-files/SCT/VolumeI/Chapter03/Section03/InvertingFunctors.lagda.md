# Functors inverting a collection

This is `con:Functors_Inverting_A_Collection`. The defining pullback
selects functors whose action on the chosen arrows lands in the core of
`Iso D`. Its projection is an embedding. Transporting through the
canonical mapping-anima/core comparison gives the object collection
spanning the full subcategory of the functor category.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section03.InvertingFunctors
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open Categories.FunctorCategories ℱ using (Fun)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; chosen-base-change-embedding; equivalence-isEmbedding; module LeftCancellation)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P using (map-preserves-embedding)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M using (mappingAction)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection; PreservesMorphisms)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q
  using (isomorphisms; isomorphismInclusion; isomorphismInclusion-isEmbedding)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S
  using (SubcategoryAxiom; SubcategoryPresentation)
open import SCT.VolumeI.Chapter03.Section02.ObjectCollections 𝒯 M P I using (ObjectCollection)
open import SCT.VolumeI.Chapter03.Section02.SpannedSubcategories 𝒯 M ℱ P I E S using (module Spanned)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategoryCharacterization 𝒯 M ℱ P I E S using (module Characterization; full-subcategory-on-equivalent-objects)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P using (IsFullSubcategory)

Inverts : {C D : CAT} → MAP C D → MorphismCollection C → Set m
Inverts {D = D} f W = PreservesMorphisms f W (isomorphisms D)

module Inverting {C : CAT} (W : MorphismCollection C) (D : CAT) where
  X = MorphismCollection.collection W
  w = MorphismCollection.inclusion W
  iso = isomorphismInclusion D

  restriction : MAP (Map C D) (Map X (Map [1] D))
  restriction = mapPre w ∘ mappingAction [1] C D

  maps : CAT
  maps = Pullback restriction (mapPost iso)

  maps-isAn : isAn maps
  maps-isAn = pullback-isAn _ _ (map-isAn C D)
    (map-isAn X (MorphismCollection.collection (isomorphisms D))) (map-isAn X (Map [1] D))

  inclusion : MAP maps (Map C D)
  inclusion = pullback₁

  inclusion-isEmbedding : IsEmbedding inclusion
  inclusion-isEmbedding = chosen-base-change-embedding restriction (mapPost iso)
    (map-preserves-embedding X iso (isomorphismInclusion-isEmbedding D))

  objects : ObjectCollection (Fun C D)
  objects = record
    { collection = maps ; collection-isAn = maps-isAn
    ; inclusion = CoreOfFun.comparison C D ∘ inclusion
    ; inclusion-isEmbedding = LeftCancellation.compose inclusion (CoreOfFun.comparison C D)
        (equivalence-isEmbedding _ (CoreOfFun.comparison-isEquiv C D)) inclusion-isEmbedding }

  module Category (L : SubcategoryAxiom) where
    module Full = Spanned L objects using (category; inclusion; presentation)

    functors : CAT
    functors = Full.category

    functorInclusion : MAP functors (Fun C D)
    functorInclusion = Full.inclusion

    isFullSubcategory : IsFullSubcategory functorInclusion
    isFullSubcategory = Characterization.isFullSubcategory objects Full.presentation

    abstract
      equivalent-objects : IsEquiv (CoreOfFun.comparison C D ∘ inclusion) → IsEquiv functorInclusion
      equivalent-objects e = full-subcategory-on-equivalent-objects objects Full.presentation e
```
