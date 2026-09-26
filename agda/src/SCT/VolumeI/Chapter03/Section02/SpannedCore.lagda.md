# The core of a spanned subcategory

For `lem:Core_Full_Subcategory`, the identity of an object supplies its
image in the chosen object collection. Conversely, the collection maps
into the subcategory by the object-factorization criterion. Embedding of
the collection and the subcategory inclusion proves the two are equivalent
over the ambient core.

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

module SCT.VolumeI.Chapter03.Section02.SpannedCore
  {c m ℓa : Level} (𝒯 : Theory c m ℓa) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (mapPost-reflect)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; embedding-reflect; embedding-cong; embedding-with-section; module LeftCancellation)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P using (map-preserves-embedding)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M using (mapPre-mapPost)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S
  using (SubcategoryPresentation)
open import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences 𝒯 M ℱ P I E S using (module Presented)
open import SCT.VolumeI.Chapter03.Section02.ObjectCollections 𝒯 M P I
open import SCT.VolumeI.Chapter03.Section02.Factorization.ObjectCollectionClosure 𝒯 M ℱ P I E S using (module Closure)
open import SCT.VolumeI.Chapter03.Section02.SpannedSubcategories 𝒯 M ℱ P I E S using (module FactorFromObjects)

core-reflect : {X C : CAT} → isAn X → (f g : MAP X (Core C)) →
  (coreInclusion C ∘ f) =₁ (coreInclusion C ∘ g) → f =₁ g
core-reflect {X} {C} xAn = mapPost-reflect (coreInclusion C) (core-universal X C xAn)

core-of-core-map : {X C : CAT} (h : MAP X (Core C)) →
  mapPost {C = One} (coreInclusion C ∘ h) =₁ (h ∘ coreInclusion X)
core-of-core-map {X} {C} h = core-reflect (core-isAn X) _ _
  (comp-assoc (coreInclusion X) h (coreInclusion C) ∙
    coreInclusion-natural (coreInclusion C ∘ h))

module CoreComparison {C : CAT} (V : ObjectCollection C)
  (A : SubcategoryPresentation (SpannedMorphisms.collectionOfMorphisms V)) where
  X = ObjectCollection.collection V
  j = ObjectCollection.inclusion V
  j-embedding = ObjectCollection.inclusion-isEmbedding V
  G = SubcategoryPresentation.subcategory A
  i = SubcategoryPresentation.inclusion A
  a = FunctorLift.lift (SubcategoryPresentation.arrows A)
  β = FunctorLift.comparison (SubcategoryPresentation.arrows A)
  e = mapPre {D = G} (terminate [1])
  source = Closure.sourceObject V

  comparison : MAP (Core G) X
  comparison = (source ∘ a) ∘ e

  identity-source : (mapPre {D = G} zero ∘ e) =₁ id (Core G)
  identity-source = mapPre-id One G ∙
    (mapPre-cong (terminal-iso (terminate [1] ∘ zero) (id One)) ∙ mapPre-comp zero (terminate [1]))

  source-on-arrows : (j ∘ (source ∘ a)) =₁ (mapPre zero ∘ mapPost i)
  source-on-arrows = (mapPre zero ◁ β) ∙
    (comp-assoc a (SpannedMorphisms.morphisms-inclusion V) (mapPre zero) ∙
      ((Closure.source-frame V ⁻¹ ▷ a) ∙ (comp-assoc a source j) ⁻¹))

  over-core : (j ∘ comparison) =₁ mapPost {C = One} i
  over-core = comp-unitʳ (mapPost i) ∙
    ((mapPost i ◁ identity-source) ∙
      (comp-assoc e (mapPre zero) (mapPost i) ∙
        ((mapPre-mapPost zero i ▷ e) ∙
          ((source-on-arrows ▷ e) ∙ (comp-assoc e (source ∘ a) j) ⁻¹))))

  objects : FunctorLift j (mapPost {C = One} (coreInclusion C ∘ j))
  objects = record { lift = coreInclusion X ; comparison = (core-of-core-map j) ⁻¹ }
  lifted = FactorFromObjects.factorization V A (coreInclusion C ∘ j) objects
  module Reverse = CoreLift (ObjectCollection.collection-isAn V) (FunctorLift.lift lifted)

  inverse : MAP X (Core G)
  inverse = Reverse.lift

  inverse-over-core : (mapPost i ∘ inverse) =₁ j
  inverse-over-core = core-reflect (ObjectCollection.collection-isAn V) _ _
    ((FunctorLift.comparison lifted) ∙
      ((i ◁ Reverse.comparison) ∙
        (comp-assoc inverse (coreInclusion G) i ∙
          ((coreInclusion-natural i ▷ inverse) ∙
            (comp-assoc inverse (mapPost i) (coreInclusion C)) ⁻¹))))

  abstract
    comparison-isEmbedding : IsEmbedding comparison
    comparison-isEmbedding = LeftCancellation.cancel comparison j j-embedding
      (embedding-cong (over-core ⁻¹)
        (map-preserves-embedding One i (Presented.inclusion-isEmbedding _ A)))

    section : (comparison ∘ inverse) =₁ id X
    section = embedding-reflect j j-embedding _ _
      ((comp-unitʳ j) ⁻¹ ∙
        (inverse-over-core ∙ ((over-core ▷ inverse) ∙ (comp-assoc inverse comparison j) ⁻¹)))

    comparison-isEquiv : IsEquiv comparison
    comparison-isEquiv = embedding-with-section comparison comparison-isEmbedding inverse section
```
