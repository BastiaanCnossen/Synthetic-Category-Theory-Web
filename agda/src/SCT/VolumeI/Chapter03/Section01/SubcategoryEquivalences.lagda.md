# Changing the presentation of a subcategory

An equivalence of sources over the ambient category preserves the
subcategory property. To prove this for the specified square, transport
the proposed family of morphisms across the equivalence, use the given
subcategory property, and lift back. The embedding pullback criterion
then supplies the universal property, including the specified matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter03.Section01.SubcategoryEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M using (mappingAction)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; IsPullback; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; embedding-cong; equivalence-isEmbedding; module LeftCancellation)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P using (map-preserves-embedding)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PullbackProjections 𝒯 P using (embedding-pullback)
open import SCT.VolumeI.Chapter03.Section01.Subcategories 𝒯 M P I

module ChangeSource {A B C : CAT} (f : MAP A C) (g : MAP B C)
  (e : MAP A B) (equivalent : IsEquiv e) (over : (g ∘ e) =₁ f)
  (full : IsSubcategory g) where

  embedding : IsEmbedding f
  embedding = embedding-cong over
    (LeftCancellation.compose e g (subcategory-isEmbedding g full)
      (equivalence-isEmbedding e equivalent))

  module Tested (D : CAT) where
    h = pullback₁ {f = mappingAction [1] D C} {mapPost (mapPost f)}
    q = pullback₂ {f = mappingAction [1] D C} {mapPost (mapPost f)}
    arrow-change = mapPost {C = Map [1] D} (mapPost {C = [1]} e)
    map-change = mapPost {C = D} e

    upper : (mapPost g ∘ map-change) =₁ mapPost f
    upper = mapPost-cong over ∙ mapPost-comp e g

    lower : (mapPost (mapPost g) ∘ arrow-change) =₁ mapPost (mapPost f)
    lower = mapPost-cong (mapPost-cong over ∙ mapPost-comp e g) ∙
      mapPost-comp (mapPost e) (mapPost g)

    cone : Cone (mappingAction [1] D C) (mapPost (mapPost g)) _
    cone = record { left = h ; right = arrow-change ∘ q
      ; match = comp-assoc q arrow-change (mapPost (mapPost g)) ∙
          ((lower ⁻¹ ▷ q) ∙ pullbackMatch) }
    module U = UniversalCone (subcategorySquare g D)
      (IsSubcategory.mapping-square-isPullback full D)
    chosen = equiv-lift (mapPost-isEquiv e equivalent) (U.factor cone)

    factorization : FunctorLift (mapPost f) h
    factorization = record { lift = FunctorLift.lift chosen
      ; comparison = ConeIso.leftIso (U.factor-β cone) ∙
          ((mapPost g ◁ FunctorLift.comparison chosen) ∙
            (comp-assoc (FunctorLift.lift chosen) map-change (mapPost g) ∙
              (upper ⁻¹ ▷ FunctorLift.lift chosen))) }

    isPullback : IsPullback (subcategorySquare f D)
    isPullback = embedding-pullback (subcategorySquare f D)
      (map-preserves-embedding (Map [1] D) (mapPost f) (map-preserves-embedding [1] f embedding))
      (map-preserves-embedding D f embedding) factorization

  isSubcategory : IsSubcategory f
  isSubcategory = record
    { morphisms-isEmbedding = map-preserves-embedding [1] f embedding
    ; mapping-square-isPullback = Tested.isPullback }

subcategory-precompose-equivalence : {A B C : CAT}
  (f : MAP A C) (g : MAP B C) (e : MAP A B) → IsEquiv e →
  (g ∘ e) =₁ f → IsSubcategory g → IsSubcategory f
subcategory-precompose-equivalence = ChangeSource.isSubcategory
```
