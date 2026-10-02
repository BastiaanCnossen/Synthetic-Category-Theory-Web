# Using the subcategory universal property

The universal property gives a factorization of every functor whose
morphisms lie in the collection. We retain the comparison over the
ambient category. It also shows directly that the inclusion is an
embedding, and that a presentation of all morphisms is an equivalence
(`lem:Subcategory_On_All_Morphisms`).

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

module SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M
  using (nameMap; nameMapIso; decodeMap; decodeMapIso; decode-name; oneProduct-in)
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M
  using (mapPost; mapPost-isEquiv; mapPost-uncurry; mapPost-comp; mapPost-cong)
open import SCT.VolumeI.Chapter01.Section03.FactorizationCalculus
  vocabulary terminal products productLaws composition
  using (lift-unique)
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M
  using (mapPost-name; post-tests-all)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; IsPullback; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; base-change-embedding; embedding-reflect)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P
  using (map-preserves-embedding; map-detects-embedding)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
  using (degenerate-pullback-converse)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M
  using (mappingAction; mappingAction-name)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I
  using (MorphismCollection; allMorphisms)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S
  using (SubcategoryPresentation; presentationSquare)
open import SCT.VolumeI.Chapter03.Section01.Subcategories 𝒯 M P I
  using (IsSubcategory; subcategorySquare)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PullbackProjections 𝒯 P using (embedding-pullback)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.TestedInclusions 𝒯 M P using (module Boundary)
open Pullbacks.PullbackStructure P

decode-post : {B C D : CAT} (f : MAP C D) (x : Obj-abs (Map B C)) →
  decodeMap (mapPost f ∘ x) =₁ (f ∘ decodeMap x)
decode-post {B} f x = comp-assoc (oneProduct-in B) (mapUncurry x) f ∙
  (mapPost-uncurry f x ▷ oneProduct-in B)

module Presented {C : CAT} (W : MorphismCollection C) (A : SubcategoryPresentation W) where
  open SubcategoryPresentation A

  inclusion-isEmbedding : IsEmbedding inclusion
  inclusion-isEmbedding = map-detects-embedding inclusion (λ D →
    base-change-embedding (presentationSquare W inclusion arrows D) (universal D)
      (map-preserves-embedding (Map [1] D) (MorphismCollection.inclusion W)
        (MorphismCollection.inclusion-isEmbedding W)))

  module SubcategorySquare (D : CAT) where
    tested = subcategorySquare inclusion D
    open Boundary [1] inclusion (MorphismCollection.inclusion W) (FunctorLift.lift arrows)
      (FunctorLift.comparison arrows) D using (cone)
    module U = UniversalCone (presentationSquare W inclusion arrows D) (universal D)

    isPullback : IsPullback tested
    isPullback = embedding-pullback tested
      (map-preserves-embedding (Map [1] D) (mapPost inclusion)
        (map-preserves-embedding [1] inclusion inclusion-isEmbedding))
      (map-preserves-embedding D inclusion inclusion-isEmbedding)
      record { lift = U.factor cone ; comparison = ConeIso.leftIso (U.factor-β cone) }

  inclusion-isSubcategory : IsSubcategory inclusion
  inclusion-isSubcategory = record
    { morphisms-isEmbedding = map-preserves-embedding [1] inclusion inclusion-isEmbedding
    ; mapping-square-isPullback = SubcategorySquare.isPullback }

  all-morphisms-isEquiv : IsEquiv (MorphismCollection.inclusion W) → IsEquiv inclusion
  all-morphisms-isEquiv em = post-tests-all inclusion (λ D →
    degenerate-pullback-converse (mapPost-isEquiv (MorphismCollection.inclusion W) em)
      (presentationSquare W inclusion arrows D) (universal D))

  module Factor {D : CAT} (f : MAP D C)
    (morphisms : FunctorLift (MorphismCollection.inclusion W) (mapPost {C = [1]} f)) where
    module U = UniversalCone (presentationSquare W inclusion arrows D) (universal D)

    cone : Cone (mappingAction [1] D C)
      (mapPost {C = Map [1] D} (MorphismCollection.inclusion W)) One
    cone = record
      { left = nameMap f
      ; right = nameMap (FunctorLift.lift morphisms)
      ; match = (mapPost-name (MorphismCollection.inclusion W) (FunctorLift.lift morphisms)) ⁻¹ ∙
          (nameMapIso ((FunctorLift.comparison morphisms) ⁻¹) ∙ mappingAction-name [1] f) }

    point : Obj-abs (Map D subcategory)
    point = U.factor cone

    factor : MAP D subcategory
    factor = decodeMap point

    comparison : (inclusion ∘ factor) =₁ f
    comparison = decode-name f ∙
      (decodeMapIso (ConeIso.leftIso (U.factor-β cone)) ∙ (decode-post inclusion point) ⁻¹)

    lift : FunctorLift inclusion f
    lift = record { lift = factor ; comparison = comparison }

  factorization-unique : {D : CAT} (f : MAP D C) (h k : FunctorLift inclusion f) →
    FunctorLift.lift h =₁ FunctorLift.lift k
  factorization-unique f = lift-unique (embedding-reflect inclusion inclusion-isEmbedding)

subcategory-on-all-morphisms : (C : CAT) (A : SubcategoryPresentation (allMorphisms C)) →
  IsEquiv (SubcategoryPresentation.inclusion A)
subcategory-on-all-morphisms C A = Presented.all-morphisms-isEquiv (allMorphisms C) A (id-isEquiv _)
```
