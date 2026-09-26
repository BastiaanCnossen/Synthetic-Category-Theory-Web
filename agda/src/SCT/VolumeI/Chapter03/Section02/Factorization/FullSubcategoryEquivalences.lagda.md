# Changing the presentation of a full subcategory

An equivalence of sources over the ambient category preserves the full
subcategory property. To prove this for the specified square, transport
the proposed family of objects across the equivalence, use fullness of
the given presentation, and lift back. The embedding pullback criterion
then supplies the universal property, including the specified matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section02.Factorization.FullSubcategoryEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; IsPullback; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; embedding-cong; equivalence-isEmbedding; module LeftCancellation)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P using (map-preserves-embedding)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PullbackProjections 𝒯 P using (embedding-pullback)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P

module ChangeSource {A B C : CAT} (f : MAP A C) (g : MAP B C)
  (e : MAP A B) (equivalent : IsEquiv e) (over : (g ∘ e) =₁ f)
  (full : IsFullSubcategory g) where

  embedding : IsEmbedding f
  embedding = embedding-cong over
    (LeftCancellation.compose e g (full-subcategory-isEmbedding g full)
      (equivalence-isEmbedding e equivalent))

  module Tested (D : CAT) where
    h = pullback₁ {f = restrictionToCores D C} {mapPost (mapPost f)}
    q = pullback₂ {f = restrictionToCores D C} {mapPost (mapPost f)}
    core-change = mapPost {C = Core D} (mapPost {C = One} e)
    map-change = mapPost {C = D} e

    upper : (mapPost g ∘ map-change) =₁ mapPost f
    upper = mapPost-cong over ∙ mapPost-comp e g

    lower : (mapPost (mapPost g) ∘ core-change) =₁ mapPost (mapPost f)
    lower = mapPost-cong (mapPost-cong over ∙ mapPost-comp e g) ∙
      mapPost-comp (mapPost e) (mapPost g)

    cone : Cone (restrictionToCores D C) (mapPost (mapPost g)) _
    cone = record { left = h ; right = core-change ∘ q
      ; match = comp-assoc q core-change (mapPost (mapPost g)) ∙
          ((lower ⁻¹ ▷ q) ∙ pullbackMatch) }
    module U = UniversalCone (fullSubcategorySquare g D)
      (IsFullSubcategory.mapping-square-isPullback full D)
    chosen = equiv-lift (mapPost-isEquiv e equivalent) (U.factor cone)

    factorization : FunctorLift (mapPost f) h
    factorization = record { lift = FunctorLift.lift chosen
      ; comparison = ConeIso.leftIso (U.factor-β cone) ∙
          ((mapPost g ◁ FunctorLift.comparison chosen) ∙
            (comp-assoc (FunctorLift.lift chosen) map-change (mapPost g) ∙
              (upper ⁻¹ ▷ FunctorLift.lift chosen))) }

    isPullback : IsPullback (fullSubcategorySquare f D)
    isPullback = embedding-pullback (fullSubcategorySquare f D)
      (map-preserves-embedding (Core D) (mapPost f) (map-preserves-embedding One f embedding))
      (map-preserves-embedding D f embedding) factorization

  isFullSubcategory : IsFullSubcategory f
  isFullSubcategory = record
    { core-isEmbedding = map-preserves-embedding One f embedding
    ; mapping-square-isPullback = Tested.isPullback }

full-subcategory-precompose-equivalence : {A B C : CAT}
  (f : MAP A C) (g : MAP B C) (e : MAP A B) → IsEquiv e →
  (g ∘ e) =₁ f → IsFullSubcategory g → IsFullSubcategory f
full-subcategory-precompose-equivalence = ChangeSource.isFullSubcategory
```
