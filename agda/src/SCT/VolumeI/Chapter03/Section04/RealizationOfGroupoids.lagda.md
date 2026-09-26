# Realization of a groupoid

For `lem:Realization_Of_A_Groupoid`, every functor from the groupoid
already inverts all its morphisms. The localization universal property
therefore says that restriction induces an equivalence on every mapping
anima. Testing on mapping animae proves the localization map equivalent.

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

module SCT.VolumeI.Chapter03.Section04.RealizationOfGroupoids
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (pre-tests-all)
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (allMorphisms)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.LocalizationUniversal 𝒯 M ℱ P I E S Q R using (module Universal)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)
open import SCT.VolumeI.Chapter03.Section04.GeometricRealization 𝒯 M ℱ P I E S Q R using (module Realization)
open import SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.InvertingFromGroupoids 𝒯 M ℱ P I E S Q R using (module FromGroupoid)

module OnGroupoids (L : SubcategoryAxiom) (Z : WithSubcategories.LocalizationAxiom L)
  (C : CAT) (groupoid : IsGroupoid C) where
  module Geom = Realization L Z using (localization; universal)
  module UP = Universal L (allMorphisms C) (Geom.localization C) (Geom.universal C) using (module Into)

  restriction-isEquiv : (D : CAT) → IsEquiv (mapPre {D = D} (Geom.localization C))
  restriction-isEquiv D = equiv-transport (UP.Into.comparison D)
    (equiv-compose (UP.Into.restriction D) (Inverting.inclusion (allMorphisms C) D)
      (UP.Into.isEquiv D) (FromGroupoid.inclusion-isEquiv C groupoid D))

  localization-isEquiv : IsEquiv (Geom.localization C)
  localization-isEquiv = pre-tests-all (Geom.localization C) restriction-isEquiv
```
