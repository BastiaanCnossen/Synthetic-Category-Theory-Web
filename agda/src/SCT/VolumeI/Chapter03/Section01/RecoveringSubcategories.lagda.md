# Recovering a subcategory from its morphisms

An existing subcategory presents its own collection of morphisms. Any two
presentations of that collection are equivalent over the ambient category.
This proves `lem:Recovering_Subcategories_From_Morphisms`.

The two universal factorizations are inverse because both inclusions are
embeddings: each composite and the identity factor the same inclusion.
Their comparisons over the ambient category remain explicit.

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

module SCT.VolumeI.Chapter03.Section01.RecoveringSubcategories
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Walking.WalkingMorphism I
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M using (mapPost)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; ConeIso; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (embedding-reflect)
open import SCT.VolumeI.Chapter01.Section03.FactorizationCalculus
  vocabulary terminal products productLaws composition
  using (lift-id; lift-compose; lift-unique)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P
  using (map-preserves-embedding)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I
  using (MorphismCollection; subcategoryMorphisms)
open import SCT.VolumeI.Chapter03.Section01.Subcategories 𝒯 M P I
  using (IsSubcategory; subcategorySquare; subcategory-isEmbedding)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S
  using (SubcategoryPresentation; presentationSquare; SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences 𝒯 M ℱ P I E S
  using (module Presented)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PullbackProjections 𝒯 P using (embedding-pullback)

module Existing {A C : CAT} (f : MAP A C) (sub : IsSubcategory f) where
  W = subcategoryMorphisms f sub
  arrows : FunctorLift (mapPost {C = [1]} f) (mapPost f)
  arrows = lift-id (mapPost f)

  universal : (D : CAT) → IsPullback (presentationSquare W f arrows D)
  universal D = embedding-pullback (presentationSquare W f arrows D)
    (map-preserves-embedding (Map [1] D) (mapPost f) (IsSubcategory.morphisms-isEmbedding sub))
    (map-preserves-embedding D f (subcategory-isEmbedding f sub))
    record { lift = U.factor (pullbackCone _ _)
      ; comparison = ConeIso.leftIso (U.factor-β (pullbackCone _ _)) }
    where module U = UniversalCone (subcategorySquare f D) (IsSubcategory.mapping-square-isPullback sub D)

  presentation : SubcategoryPresentation W
  presentation = record { subcategory = A ; inclusion = f ; arrows = arrows ; universal = universal }

module PresentationComparison {C : CAT} (W : MorphismCollection C)
  (A B : SubcategoryPresentation W) where
  module A = SubcategoryPresentation A
  module B = SubcategoryPresentation B
  module Forward = Presented.Factor W B A.inclusion A.arrows using (factor; comparison; lift)
  module Backward = Presented.Factor W A B.inclusion B.arrows using (factor; comparison; lift)

  functor : MAP A.subcategory B.subcategory
  functor = Forward.factor

  over-C : (B.inclusion ∘ functor) =₁ A.inclusion
  over-C = Forward.comparison

  backward-forward : (Backward.factor ∘ functor) =₁ id A.subcategory
  backward-forward = lift-unique
    (embedding-reflect A.inclusion (Presented.inclusion-isEmbedding W A))
    (lift-compose Backward.lift Forward.lift) (lift-id A.inclusion)

  forward-backward : (functor ∘ Backward.factor) =₁ id B.subcategory
  forward-backward = lift-unique
    (embedding-reflect B.inclusion (Presented.inclusion-isEmbedding W B))
    (lift-compose Forward.lift Backward.lift) (lift-id B.inclusion)

  isEquiv : IsEquiv functor
  isEquiv = record { inverse = Backward.factor
    ; sectionIso = backward-forward ⁻¹ ; retractionIso = forward-backward ⁻¹ }

module Recovery {A C : CAT} (f : MAP A C) (sub : IsSubcategory f)
  (G : SubcategoryPresentation (subcategoryMorphisms f sub)) where
  module Compare = PresentationComparison (subcategoryMorphisms f sub) G (Existing.presentation f sub)
    using (functor; over-C; isEquiv)

  recovery : MAP (SubcategoryPresentation.subcategory G) A
  recovery = Compare.functor

  recovery-over-C : (f ∘ recovery) =₁ SubcategoryPresentation.inclusion G
  recovery-over-C = Compare.over-C

  recovery-isEquiv : IsEquiv recovery
  recovery-isEquiv = Compare.isEquiv
```

Applying the axiom to the closed collection of morphisms of an existing
subcategory gives the constructor used in the manuscript's statement.

```agda
open import SCT.VolumeI.Chapter03.Section01.SubcategoryClosure 𝒯 M ℱ P I E S
  using (subcategory-morphisms-closed)

module Reconstruct (L : SubcategoryAxiom) {A C : CAT} (f : MAP A C) (sub : IsSubcategory f) where
  presentation : SubcategoryPresentation (subcategoryMorphisms f sub)
  presentation = SubcategoryAxiom.generated L (subcategoryMorphisms f sub)
    (subcategory-morphisms-closed f sub)
  open Recovery f sub presentation public
    using (recovery; recovery-over-C; recovery-isEquiv)
```
