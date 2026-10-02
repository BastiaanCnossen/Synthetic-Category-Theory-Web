# The mapping-anima characterization of a full subcategory

These are `prop:Full_Subcategory_Is_Full_Subcategory` and
`prop:Characterization_Full_Subcategory`. The family factorization lemma
gives the existence part of each pullback. The inclusion is an embedding,
so the embedding pullback criterion supplies the full universal property.
The specified square includes the comparison on cores proved earlier.

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

module SCT.VolumeI.Chapter03.Section02.FullSubcategoryCharacterization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P using (map-preserves-embedding)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M using (mappingAction; mappingAction-natural)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryPresentation)
open import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences 𝒯 M ℱ P I E S using (module Presented)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PullbackProjections 𝒯 P using (embedding-pullback)
open import SCT.VolumeI.Chapter03.Section02.ObjectCollections 𝒯 M P I
open import SCT.VolumeI.Chapter03.Section02.SpannedCore 𝒯 M ℱ P I E S using (module CoreComparison)
open import SCT.VolumeI.Chapter03.Section02.Factorization.ObjectFactorizationFamilies 𝒯 M ℱ P I E S using (module Factor)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.TestedInclusions 𝒯 M P using (module Boundary)

module Characterization {C : CAT} (V : ObjectCollection C)
  (A : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms V)) where
  G = SubcategoryPresentation.subcategory A
  i = SubcategoryPresentation.inclusion A
  X = ObjectCollection.collection V
  j = ObjectCollection.inclusion V
  module Core = CoreComparison V A using (comparison; over-core)

  boundary : (D : CAT) → (mapPost {C = Core D} j ∘ mapPost Core.comparison) =₁ mapPost (mapPost i)
  boundary D = mapPost-cong Core.over-core ∙ mapPost-comp Core.comparison j

  square : (D : CAT) → Cone (restrictionToCores D C) (mapPost j) (Map D G)
  square D = record
    { left = mapPost i ; right = mapPost Core.comparison ∘ restrictionToCores D G
    ; match = comp-assoc (restrictionToCores D G) (mapPost Core.comparison) (mapPost j) ∙
        ((boundary D ⁻¹ ▷ restrictionToCores D G) ∙ (mappingAction-natural One D i) ⁻¹) }

  module Tested (D : CAT) where
    h = pullback₁ {f = restrictionToCores D C} {mapPost j}
    objects = pullback₂ {f = restrictionToCores D C} {mapPost j}
    parameter-isAn : isAn (Pullback (restrictionToCores D C) (mapPost j))
    parameter-isAn = pullback-isAn _ _ (map-isAn D C) (map-isAn (Core D) X)
      (map-isAn (Core D) (Core C))

    isPullback : IsPullback (square D)
    isPullback = embedding-pullback (square D)
      (map-preserves-embedding (Core D) j (ObjectCollection.inclusion-isEmbedding V))
      (map-preserves-embedding D i (Presented.inclusion-isEmbedding _ A))
      (Factor.factorization V A parameter-isAn h objects pullbackMatch)

  module FullSquare (D : CAT) where
    open Boundary One i j Core.comparison Core.over-core D using (h; q; cone)
    parameter-isAn : isAn (Pullback (restrictionToCores D C) (mapPost (mapPost i)))
    parameter-isAn = pullback-isAn _ _ (map-isAn D C) (map-isAn (Core D) (Core G))
      (map-isAn (Core D) (Core C))
    objects = mapPost Core.comparison ∘ q
    match : (restrictionToCores D C ∘ h) =₁ (mapPost j ∘ objects)
    match = Cone.match cone

    isPullback : IsPullback (fullSubcategorySquare i D)
    isPullback = embedding-pullback (fullSubcategorySquare i D)
      (map-preserves-embedding (Core D) (mapPost i)
        (map-preserves-embedding One i (Presented.inclusion-isEmbedding _ A)))
      (map-preserves-embedding D i (Presented.inclusion-isEmbedding _ A))
      (Factor.factorization V A parameter-isAn h objects match)

  isFullSubcategory : IsFullSubcategory i
  isFullSubcategory = record
    { core-isEmbedding = map-preserves-embedding One i (Presented.inclusion-isEmbedding _ A)
    ; mapping-square-isPullback = FullSquare.isPullback }

open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (pullback-equivalence)

full-subcategory-on-all-objects : (C : CAT)
  (A : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms (allObjects C))) →
  IsEquiv (SubcategoryPresentation.inclusion A)
full-subcategory-on-all-objects C A = Presented.all-morphisms-isEquiv _ A
  (pullback-equivalence (endpoints C) (productMap (id (Core C)) (id (Core C)))
    (equiv-transport ((productMap-id (Core C) (Core C)) ⁻¹) (id-isEquiv (Core C × Core C))))
```

More generally, an equivalent collection of objects spans the whole category.

```agda
open import SCT.VolumeI.Chapter03.Section02.Factorization.ProductEmbeddings 𝒯 P using (productMap-isEquiv)

abstract
  full-subcategory-on-equivalent-objects : {C : CAT} (V : ObjectCollection C)
    (A : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms V)) →
    IsEquiv (ObjectCollection.inclusion V) → IsEquiv (SubcategoryPresentation.inclusion A)
  full-subcategory-on-equivalent-objects {C} V A ej = Presented.all-morphisms-isEquiv (SpannedMorphisms.collectionOfMorphisms V) A
    (pullback-equivalence (endpoints C) (productMap j j) (productMap-isEquiv j j ej ej))
    where
    j : MAP (ObjectCollection.collection V) (Core C)
    j = ObjectCollection.inclusion V
```
