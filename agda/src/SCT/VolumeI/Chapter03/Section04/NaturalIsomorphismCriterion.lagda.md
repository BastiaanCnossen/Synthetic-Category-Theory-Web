# A natural transformation is an isomorphism exactly when its components are

This is the unconditional `prop:Objectwise_Criterion_Natural_Isomorphisms`.
The groupoid theorem supplies fullness of `Iso D → Ar D`. The component
condition uses the universal family of objects, so anima-parametrized
objects are included.
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
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition
import SCT.VolumeI.Chapter01.Section05.Initial as Initial

module SCT.VolumeI.Chapter03.Section04.NaturalIsomorphismCriterion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (N : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I using (NatTrans; nameFun)
open Rezk 𝒯 M ℱ P I E using (IsoLift)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section04.FundamentalGroupoids 𝒯 M ℱ P I E S Q R N using (module Consequences)
open import SCT.VolumeI.Chapter03.Section04.ObjectwiseNaturalIsomorphisms 𝒯 M ℱ P I E R using (module Transformation)

module Criterion (L : SubcategoryAxiom) (Z : WithSubcategories.LocalizationAxiom L)
  (C D : CAT) (α : NatTrans C D) where
  open Transformation C D α public using (components; ComponentsInvertible)

  abstract
    from-components : ComponentsInvertible → IsoLift (nameFun α)
    from-components = Transformation.FromComponents.isNaturalIso C D α
      (Consequences.isoArrow-isFullSubcategory L Z D)

    to-components : IsoLift (nameFun α) → ComponentsInvertible
    to-components = Transformation.FromNaturalIso.components-invertible C D α
```