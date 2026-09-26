# The subcategory spanned by a collection of objects

This is `def:Full_Subcategory_Spanned_By`. The associated morphism
collection is closed under composition, so the subcategory axiom applies.
A functor whose core lands in the chosen objects factors through this
subcategory: both endpoints of each of its arrows lie in the collection.

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

module SCT.VolumeI.Chapter03.Section02.SpannedSubcategories
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M using (mapPre-mapPost)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S
open import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences 𝒯 M ℱ P I E S
  using (module Presented)
open import SCT.VolumeI.Chapter03.Section02.ObjectCollections 𝒯 M P I
open import SCT.VolumeI.Chapter03.Section02.Factorization.ObjectCollectionClosure 𝒯 M ℱ P I E S
  using (object-collection-morphisms-closed; module Closure)

module Spanned (L : SubcategoryAxiom) {C : CAT} (V : ObjectCollection C) where
  abstract
    presentation : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms V)
    presentation = SubcategoryAxiom.generated L (SpannedMorphisms.collectionOfMorphisms V)
      (object-collection-morphisms-closed V)

  category : CAT
  category = SubcategoryPresentation.subcategory presentation

  inclusion : MAP category C
  inclusion = SubcategoryPresentation.inclusion presentation

module FactorFromObjects {C : CAT} (V : ObjectCollection C)
  (A : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms V))
  {D : CAT} (f : MAP D C) (objects : FunctorLift (ObjectCollection.inclusion V) (mapPost {C = One} f)) where
  j = ObjectCollection.inclusion V
  k = FunctorLift.lift objects
  β = FunctorLift.comparison objects

  endpoint : (x : Obj-abs [1]) →
    (mapPre x ∘ mapPost f) =₁ (j ∘ (k ∘ mapPre x))
  endpoint x = comp-assoc (mapPre x) k j ∙
    ((β ⁻¹ ▷ mapPre x) ∙ mapPre-mapPost x f)

  arrows : FunctorLift (SpannedMorphisms.morphisms-inclusion V) (mapPost {C = [1]} f)
  arrows = Closure.lift-endpoints V (mapPost f)
    (k ∘ mapPre zero) (k ∘ mapPre one) (endpoint zero) (endpoint one)

  factorization : FunctorLift (SubcategoryPresentation.inclusion A) f
  factorization = Presented.Factor.lift (SpannedMorphisms.collectionOfMorphisms V) A f arrows
```
