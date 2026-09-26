# Lifting identifications through a localization

Restriction along a localization is an embedding on mapping animae:
it factors as the localization equivalence followed by the inclusion of
inverting functors. Thus an identification after restriction lifts with
its specified image. `Between.image` retains this higher comparison.

This interface is intended for diagrams whose prescribed commutativity
must survive passage to the localization, including geometric realization.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationIdentificationLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; embedding-cong; equivalence-isEmbedding; module LeftCancellation)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationMappingProperty 𝒯 M ℱ P I E S Q R
  using (MappingUniversalProperty; mapping-universal-property)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.RestrictionLifting 𝒯 M P using (module Lift)

module Identification (L : SubcategoryAxiom) {C T : CAT} (W : MorphismCollection C)
  (l : MAP C T) (localization : WithSubcategories.IsLocalization L W l) where

  property = mapping-universal-property L W l localization

  abstract
    restriction-isEmbedding : (D : CAT) → IsEmbedding (mapPre {D = D} l)
    restriction-isEmbedding D = embedding-cong (MappingUniversalProperty.comparison property D)
      (LeftCancellation.compose (MappingUniversalProperty.restriction property D)
        (Inverting.inclusion W D) (Inverting.inclusion-isEmbedding W D)
        (equivalence-isEmbedding (MappingUniversalProperty.restriction property D)
          (MappingUniversalProperty.isEquiv property D)))

  module Between {D : CAT} (f g : MAP T D) (α : (f ∘ l) =₁ (g ∘ l)) where
    open Lift l (restriction-isEmbedding D) f g α public
      using (lift; image; factorization)
```
