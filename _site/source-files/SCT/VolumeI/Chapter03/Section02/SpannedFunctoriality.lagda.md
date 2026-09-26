# Functoriality for spanned full subcategories

A functor preserving the chosen objects induces a functor on their full
subcategories. The core comparison reduces this to the object-factorization
criterion. The result retains its comparison over the ambient functor.

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

module SCT.VolumeI.Chapter03.Section02.SpannedFunctoriality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryPresentation)
open import SCT.VolumeI.Chapter03.Section02.ObjectCollections 𝒯 M P I
open import SCT.VolumeI.Chapter03.Section02.SpannedCore 𝒯 M ℱ P I E S using (module CoreComparison)
open import SCT.VolumeI.Chapter03.Section02.SpannedSubcategories 𝒯 M ℱ P I E S using (module FactorFromObjects)

PreservesObjects : {C D : CAT} → MAP C D → ObjectCollection C → ObjectCollection D → Set m
PreservesObjects f V W = FunctorLift (ObjectCollection.inclusion W)
  (mapPost {C = One} f ∘ ObjectCollection.inclusion V)

module Induced {C D : CAT} {V : ObjectCollection C} {W : ObjectCollection D}
  (A : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms V))
  (B : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms W))
  (f : MAP C D) (preserves : PreservesObjects f V W) where
  module Source = CoreComparison V A using (comparison; over-core)
  i = SubcategoryPresentation.inclusion A
  k = FunctorLift.lift preserves
  objects : FunctorLift (ObjectCollection.inclusion W) (mapPost {C = One} (f ∘ i))
  objects = record { lift = k ∘ Source.comparison
    ; comparison = mapPost-comp i f ∙
        ((mapPost f ◁ Source.over-core) ∙
          (comp-assoc Source.comparison (ObjectCollection.inclusion V) (mapPost f) ∙
            ((FunctorLift.comparison preserves ▷ Source.comparison) ∙
              (comp-assoc Source.comparison k (ObjectCollection.inclusion W)) ⁻¹))) }

  abstract
    factorization : FunctorLift (SubcategoryPresentation.inclusion B) (f ∘ i)
    factorization = FactorFromObjects.factorization W B (f ∘ i) objects
```
