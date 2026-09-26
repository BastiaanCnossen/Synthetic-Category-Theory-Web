# Restriction along a localization is a full subcategory

The localization universal property identifies its functor category
with the full subcategory of functors inverting the collection.
Transfer fullness along this equivalence, retaining the comparison
with ordinary restriction.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationFullSubcategory
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPre)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P using (IsFullSubcategory)
open import SCT.VolumeI.Chapter03.Section02.Factorization.FullSubcategoryEquivalences 𝒯 M P
  using (full-subcategory-precompose-equivalence)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationRestriction 𝒯 M ℱ P I E S Q R using (module RestrictionAlong)

abstract
  localization-restriction-isFullSubcategory : (L : SubcategoryAxiom) {C T : CAT}
    (W : MorphismCollection C) (l : MAP C T) → WithSubcategories.IsLocalization L W l →
    (D : CAT) → IsFullSubcategory (funPre {D = D} l)
  localization-restriction-isFullSubcategory L W l localization D =
    full-subcategory-precompose-equivalence (funPre l) Full.functorInclusion
      Restriction.functor (IsLocalization.universal localization D) Restriction.comparison Full.isFullSubcategory
    where
    open WithSubcategories L using (IsLocalization)
    module Full = Inverting.Category W D L using (functorInclusion; isFullSubcategory)
    module Restriction = RestrictionAlong L W l (IsLocalization.inverts localization) D using (functor; comparison)
```
