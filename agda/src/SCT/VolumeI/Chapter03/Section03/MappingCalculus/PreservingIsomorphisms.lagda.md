# Every functor preserves isomorphisms

This is `prop:Every_Functor_Preserves_Isomorphisms`. Rezk identifies
isomorphisms with constant arrows. Restriction of the mapping action
then shows, for the entire anima of functors at once, that the action
on isomorphisms lands in isomorphisms. This supplies a section of the
defining embedding, hence an equivalence.

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

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.PreservingIsomorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (embedding-with-section)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M using (mappingAction)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingRestriction 𝒯 M using (mappingAction-restrict)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M using (mapPre-mapPost)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q
open WithRezk R
open Rezk 𝒯 M ℱ P I E using (Iso)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategoryCharacterization 𝒯 M ℱ P I E S
  using (full-subcategory-on-equivalent-objects)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)

import SCT.VolumeI.Chapter03.Section03.MappingCalculus.PreservingIsomorphismMaps as PreservationMaps

module Preservation (C D : CAT) where
  open PreservationMaps.Preservation 𝒯 M ℱ P I E S Q R C D public
    using (family; comparison; maps-isEquiv)

  object-inclusion-isEquiv : IsEquiv (CoreOfFun.comparison C D ∘ Inverting.inclusion (isomorphisms C) D)
  object-inclusion-isEquiv = equiv-compose (Inverting.inclusion (isomorphisms C) D) (CoreOfFun.comparison C D)
    maps-isEquiv (CoreOfFun.comparison-isEquiv C D)

  functors-isEquiv = λ (L : SubcategoryAxiom) →
    Inverting.Category.equivalent-objects {C = C} (isomorphisms C) D L object-inclusion-isEquiv
```
