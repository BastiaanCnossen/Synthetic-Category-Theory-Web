# The mapping universal property as a proof interface

The restriction, its comparison with ordinary precomposition, and its
equivalence proof are kept together. This is a proved consequence of
the localization definition. Keeping this interface abstract lets later
arguments use the universal property without unfolding the chosen full
subcategory at every occurrence.

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

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationMappingProperty
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
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (Inverts; module Inverting)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationRestriction 𝒯 M ℱ P I E S Q R using (module RestrictionAlong)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationMapping 𝒯 M ℱ P I E S Q using (module OnMaps)

open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationMappingInterface 𝒯 M ℱ P I E S Q R
  public using (MappingUniversalProperty)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationMappingInterface 𝒯 M ℱ P I E S Q R
  using (mapping-from-functors)

abstract
  mapping-universal-property : (L : SubcategoryAxiom) {C T : CAT} (W : MorphismCollection C)
    (l : MAP C T) → WithSubcategories.IsLocalization L W l → MappingUniversalProperty W l
  mapping-universal-property L {C} {T} W l (record { inverts = inverts ; universal = universal }) =
    mapping-from-functors L {C = C} {T = T} W l
      (λ D → RestrictionAlong.functor L {C = C} {T = T} W l inverts D)
      (λ D → RestrictionAlong.comparison L {C = C} {T = T} W l inverts D)
      universal
```