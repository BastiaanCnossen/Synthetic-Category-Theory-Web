# Pulling back a full subcategory

This is `lem:Pullback_Of_Full_Subcategories`. Pull back the object
collection on cores. Its spanned subcategory maps to the original one.
To prove the resulting square is a pullback, factor the universal
pullback projection using the induced lift on cores, then apply the
embedding pullback criterion.

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

module SCT.VolumeI.Chapter03.Section02.FullSubcategoryPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; core-isAn)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P using (chosen-base-change-embedding)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryPresentation)
open import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences 𝒯 M ℱ P I E S using (module Presented)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PullbackProjections 𝒯 P using (embedding-pullback)
open import SCT.VolumeI.Chapter03.Section02.ObjectCollections 𝒯 M P I
open import SCT.VolumeI.Chapter03.Section02.SpannedCore 𝒯 M ℱ P I E S using (module CoreComparison)
open import SCT.VolumeI.Chapter03.Section02.SpannedSubcategories 𝒯 M ℱ P I E S using (module FactorFromObjects)

module BaseChange {B C : CAT} (f : MAP B C) (V : ObjectCollection C) where
  X = ObjectCollection.collection V
  j = ObjectCollection.inclusion V
  objects = Pullback (mapPost {C = One} f) j
  objects-inclusion = pullback₁ {f = mapPost {C = One} f} {j}
  objects-map = pullback₂ {f = mapPost {C = One} f} {j}

  collection : ObjectCollection B
  collection = record
    { collection = objects
    ; collection-isAn = pullback-isAn _ _ (core-isAn B)
        (ObjectCollection.collection-isAn V) (core-isAn C)
    ; inclusion = objects-inclusion
    ; inclusion-isEmbedding = chosen-base-change-embedding (mapPost f) j
        (ObjectCollection.inclusion-isEmbedding V) }

  module Square
    (A : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms V))
    (H : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms collection)) where
    i = SubcategoryPresentation.inclusion A
    k = SubcategoryPresentation.inclusion H
    module Source = CoreComparison collection H
    module Target = CoreComparison V A

    restriction-on-objects : FunctorLift j (mapPost {C = One} (f ∘ k))
    restriction-on-objects = record { lift = objects-map ∘ Source.comparison
      ; comparison = mapPost-comp k f ∙
          ((mapPost f ◁ Source.over-core) ∙
            (comp-assoc Source.comparison objects-inclusion (mapPost f) ∙
              ((pullbackMatch ⁻¹ ▷ Source.comparison) ∙
                (comp-assoc Source.comparison objects-map j) ⁻¹))) }
    induced = FactorFromObjects.factorization V A (f ∘ k) restriction-on-objects

    cone : Cone f i (SubcategoryPresentation.subcategory H)
    cone = record { left = k ; right = FunctorLift.lift induced
      ; match = (FunctorLift.comparison induced) ⁻¹ }

    p = pullback₁ {f = f} {i}
    q = pullback₂ {f = f} {i}
    object-cone : Cone (mapPost f) j (Core (Pullback f i))
    object-cone = record
      { left = mapPost p ; right = Target.comparison ∘ mapPost q
      ; match = comp-assoc (mapPost q) Target.comparison j ∙
          ((Target.over-core ⁻¹ ▷ mapPost q) ∙
            ((mapPost-comp q i) ⁻¹ ∙
              (mapPost-cong pullbackMatch ∙ mapPost-comp p f))) }
    object-lift : FunctorLift objects-inclusion (mapPost {C = One} p)
    object-lift = record { lift = pullbackLift object-cone ; comparison = pullbackLift-β₁ object-cone }

    isPullback : IsPullback cone
    isPullback = embedding-pullback cone
      (Presented.inclusion-isEmbedding _ A) (Presented.inclusion-isEmbedding _ H)
      (FactorFromObjects.factorization collection H p object-lift)
```
