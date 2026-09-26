# Geometric realization

For `def:Geometric_Realization`, localize at all morphisms. Functoriality is the specialization of
`LocalizationFunctoriality.Induced` using `preserves-all` below.
For `lem:Fundamental_Groupoid_Functor_Left_Adjoint_To_Inclusion`, compose
the localization equivalence with the equivalence saying that every
functor into a groupoid inverts the chosen collection.

This module does not yet assert that the realization is a groupoid.
That is the substantive theorem following the equivalent criteria.

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

module SCT.VolumeI.Chapter03.Section04.GeometricRealization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Categories.FunctorCategories ℱ using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPre)
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I
  using (allMorphisms; PreservesMorphisms)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationRestriction 𝒯 M ℱ P I E S Q R using (module RestrictionAlong)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingGroupoids 𝒯 M ℱ P I E S Q R
  using (inverting-functors-into-groupoid)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)

open import SCT.VolumeI.Chapter03.Section03.LocalizationGroupoids 𝒯 M ℱ P I E S Q R using (module IntoGroupoids)

module Realization (L : SubcategoryAxiom) (Z : WithSubcategories.LocalizationAxiom L) where
  open WithSubcategories L
  chosen : (C : CAT) → Localization (allMorphisms C)
  chosen C = LocalizationAxiom.localized Z (allMorphisms C)

  category : CAT → CAT
  category C = Localization.category (chosen C)

  localization : (C : CAT) → MAP C (category C)
  localization C = Localization.functor (chosen C)

  universal : (C : CAT) → IsLocalization (allMorphisms C) (localization C)
  universal C = Localization.isLocalization (chosen C)

  preserves-all : {C D : CAT} (f : MAP C D) → PreservesMorphisms f (allMorphisms C) (allMorphisms D)
  preserves-all f = record { lift = mapPost f
    ; comparison = (comp-unitʳ (mapPost f)) ⁻¹ ∙ comp-unitˡ (mapPost f) }

  into-groupoid = λ (C D : CAT) (groupoid : IsGroupoid D) →
    IntoGroupoids.At.isEquiv L (allMorphisms C) (localization C) (universal C) D groupoid
```
