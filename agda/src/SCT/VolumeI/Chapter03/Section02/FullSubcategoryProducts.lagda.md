# Products of spanned full subcategories

This is `lem:Full_Subcategory_Former_Commutes_With_Products`. The product
collection is transported through the canonical equivalence on cores.
Projecting its objects gives the comparison functor; pairing objects
gives the reverse factorization. The embedding criterion proves that
the comparison is an equivalence over the ambient product.

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

module SCT.VolumeI.Chapter03.Section02.FullSubcategoryProducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section04.MappingProducts 𝒯 M using (module ProductComparison)
open import SCT.VolumeI.Chapter01.Section04.Composition 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; equivalence-isEmbedding; embedding-cong; embedding-reflect; embedding-with-section; module LeftCancellation)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryPresentation)
open import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences 𝒯 M ℱ P I E S using (module Presented)
open import SCT.VolumeI.Chapter03.Section02.ObjectCollections 𝒯 M P I
open import SCT.VolumeI.Chapter03.Section02.Factorization.ProductEmbeddings 𝒯 P using (productMap-isEmbedding)
open import SCT.VolumeI.Chapter03.Section02.SpannedCore 𝒯 M ℱ P I E S using (module CoreComparison)
open import SCT.VolumeI.Chapter03.Section02.SpannedSubcategories 𝒯 M ℱ P I E S using (module FactorFromObjects)

module ProductObjects {C D : CAT} (V : ObjectCollection C) (W : ObjectCollection D) where
  X = ObjectCollection.collection V
  Y = ObjectCollection.collection W
  j = ObjectCollection.inclusion V
  k = ObjectCollection.inclusion W
  module CoreProduct = ProductComparison One C D
  inclusion = CoreProduct.backward ∘ productMap j k

  collection : ObjectCollection (C × D)
  collection = record
    { collection = X × Y
    ; collection-isAn = product-isAn (ObjectCollection.collection-isAn V) (ObjectCollection.collection-isAn W)
    ; inclusion = inclusion
    ; inclusion-isEmbedding = LeftCancellation.compose (productMap j k) CoreProduct.backward
        (equivalence-isEmbedding _ (equiv-inverse CoreProduct.forward-isEquiv))
        (productMap-isEmbedding j k (ObjectCollection.inclusion-isEmbedding V) (ObjectCollection.inclusion-isEmbedding W)) }

  first : (mapPost pr₁ ∘ inclusion) =₁ (j ∘ pr₁)
  first = pair-β₁ (j ∘ pr₁) (k ∘ pr₂) ∙
    ((CoreProduct.forward-backward-first ▷ productMap j k) ∙
      (comp-assoc (productMap j k) CoreProduct.backward (mapPost pr₁)) ⁻¹)
  second : (mapPost pr₂ ∘ inclusion) =₁ (k ∘ pr₂)
  second = pair-β₂ (j ∘ pr₁) (k ∘ pr₂) ∙
    ((CoreProduct.forward-backward-second ▷ productMap j k) ∙
      (comp-assoc (productMap j k) CoreProduct.backward (mapPost pr₂)) ⁻¹)

  module SpannedProduct
    (A : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms V))
    (B : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms W))
    (H : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms collection)) where
    i = SubcategoryPresentation.inclusion A
    l = SubcategoryPresentation.inclusion B
    h = SubcategoryPresentation.inclusion H
    module Left = CoreComparison V A using (comparison; over-core)
    module Right = CoreComparison W B using (comparison; over-core)
    module Whole = CoreComparison collection H using (comparison; over-core)

    first-objects : FunctorLift j (mapPost {C = One} (pr₁ ∘ h))
    first-objects = record { lift = pr₁ ∘ Whole.comparison
      ; comparison = mapPost-comp h pr₁ ∙
          ((mapPost pr₁ ◁ Whole.over-core) ∙
            (comp-assoc Whole.comparison inclusion (mapPost pr₁) ∙
              ((first ⁻¹ ▷ Whole.comparison) ∙ (comp-assoc Whole.comparison pr₁ j) ⁻¹))) }
    second-objects : FunctorLift k (mapPost {C = One} (pr₂ ∘ h))
    second-objects = record { lift = pr₂ ∘ Whole.comparison
      ; comparison = mapPost-comp h pr₂ ∙
          ((mapPost pr₂ ◁ Whole.over-core) ∙
            (comp-assoc Whole.comparison inclusion (mapPost pr₂) ∙
              ((second ⁻¹ ▷ Whole.comparison) ∙ (comp-assoc Whole.comparison pr₂ k) ⁻¹))) }
    first-lift = FactorFromObjects.factorization V A (pr₁ ∘ h) first-objects
    second-lift = FactorFromObjects.factorization W B (pr₂ ∘ h) second-objects

    forward : MAP (SubcategoryPresentation.subcategory H)
      (SubcategoryPresentation.subcategory A × SubcategoryPresentation.subcategory B)
    forward = pair (FunctorLift.lift first-lift) (FunctorLift.lift second-lift)
    ambient = productMap i l
    over-ambient : (ambient ∘ forward) =₁ h
    over-ambient = pair-η h ∙
      (pair-cong (FunctorLift.comparison first-lift) (FunctorLift.comparison second-lift) ∙
        productMap-pair i l (FunctorLift.lift first-lift) (FunctorLift.lift second-lift))

    object-pair = pair (Left.comparison ∘ mapPost pr₁) (Right.comparison ∘ mapPost pr₂)
    left-image : (mapPost pr₁ ∘ (inclusion ∘ object-pair)) =₁ (mapPost i ∘ mapPost pr₁)
    left-image = (Left.over-core ▷ mapPost pr₁) ∙
      ((comp-assoc (mapPost pr₁) Left.comparison j) ⁻¹ ∙
        ((j ◁ pair-β₁ _ _) ∙
          (comp-assoc object-pair pr₁ j ∙
            ((first ▷ object-pair) ∙ (comp-assoc object-pair inclusion (mapPost pr₁)) ⁻¹))))
    right-image : (mapPost pr₂ ∘ (inclusion ∘ object-pair)) =₁ (mapPost l ∘ mapPost pr₂)
    right-image = (Right.over-core ▷ mapPost pr₂) ∙
      ((comp-assoc (mapPost pr₂) Right.comparison k) ⁻¹ ∙
        ((k ◁ pair-β₂ _ _) ∙
          (comp-assoc object-pair pr₂ k ∙
            ((second ▷ object-pair) ∙ (comp-assoc object-pair inclusion (mapPost pr₂)) ⁻¹))))
    left-ambient : (mapPost {C = One} pr₁ ∘ mapPost ambient) =₁ (mapPost i ∘ mapPost pr₁)
    left-ambient = (mapPost-comp pr₁ i) ⁻¹ ∙
      (mapPost-cong (pair-β₁ (i ∘ pr₁) (l ∘ pr₂)) ∙ mapPost-comp ambient pr₁)
    right-ambient : (mapPost {C = One} pr₂ ∘ mapPost ambient) =₁ (mapPost l ∘ mapPost pr₂)
    right-ambient = (mapPost-comp pr₂ l) ⁻¹ ∙
      (mapPost-cong (pair-β₂ (i ∘ pr₁) (l ∘ pr₂)) ∙ mapPost-comp ambient pr₂)

    object-lift : FunctorLift inclusion (mapPost {C = One} ambient)
    object-lift = record { lift = object-pair
      ; comparison = equiv-reflect CoreProduct.forward-isEquiv _ _
          ((pair-pre (mapPost pr₁) (mapPost pr₂) (mapPost ambient)) ⁻¹ ∙
            (pair-cong (left-ambient ⁻¹ ∙ left-image) (right-ambient ⁻¹ ∙ right-image) ∙
              pair-pre (mapPost pr₁) (mapPost pr₂) (inclusion ∘ object-pair))) }
    reverse = FactorFromObjects.factorization collection H ambient object-lift
    ambient-isEmbedding = productMap-isEmbedding i l
      (Presented.inclusion-isEmbedding _ A) (Presented.inclusion-isEmbedding _ B)
    forward-isEmbedding = LeftCancellation.cancel forward ambient ambient-isEmbedding
      (embedding-cong (over-ambient ⁻¹) (Presented.inclusion-isEmbedding _ H))
    section : (forward ∘ FunctorLift.lift reverse) =₁ id _
    section = embedding-reflect ambient ambient-isEmbedding _ _
      ((comp-unitʳ ambient) ⁻¹ ∙
        (FunctorLift.comparison reverse ∙
          ((over-ambient ▷ FunctorLift.lift reverse) ∙
            (comp-assoc (FunctorLift.lift reverse) forward ambient) ⁻¹)))

    isEquiv : IsEquiv forward
    isEquiv = embedding-with-section forward forward-isEmbedding (FunctorLift.lift reverse) section
```
