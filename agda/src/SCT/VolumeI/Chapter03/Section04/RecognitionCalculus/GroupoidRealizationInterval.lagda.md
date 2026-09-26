# If the realized interval is a groupoid, it is contractible

This proves `(1) ⇒ (2)` in
`prop:Equivalent_Conditions_Geometric_Realization` independently of the
fundamental groupoid theorem. Test the terminal projection against
groupoids. Localization restriction and constant arrows are both
equivalences for those targets. The two tests at the source and target
then detect the desired equivalence.
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

module SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.GroupoidRealizationInterval
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (pre-tests-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I using (identityArrow)
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
open import SCT.VolumeI.Chapter02.Section04.BasicClosure 𝒯 M ℱ P I E R using (terminal-isGroupoid)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (allMorphisms)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q using (constantMap; core-constant)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationMappingProperty 𝒯 M ℱ P I E S Q R
  using (MappingUniversalProperty; mapping-universal-property)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingGroupoids 𝒯 M ℱ P I E S Q R
  using (inverting-maps-into-groupoid)

module Interval (L : SubcategoryAxiom) (T : CAT) (l : MAP [1] T)
  (localization : WithSubcategories.IsLocalization L (allMorphisms [1]) l) where
  property : MappingUniversalProperty (allMorphisms [1]) l
  property = mapping-universal-property L (allMorphisms [1]) l localization

  module Tested (D : CAT) (groupoid : IsGroupoid D) where
    abstract
      localization-test : IsEquiv (mapPre {D = D} l)
      localization-test = equiv-transport (MappingUniversalProperty.comparison property D)
        (equiv-compose (MappingUniversalProperty.restriction property D)
          (Inverting.inclusion (allMorphisms [1]) D)
          (MappingUniversalProperty.isEquiv property D)
          (inverting-maps-into-groupoid (allMorphisms [1]) D groupoid))

      constant-test : IsEquiv (constantMap D)
      constant-test = equiv-transport (core-constant D)
        (equiv-compose (mapPost {C = One} (identityArrow {D})) (CoreOfFun.uncurrying [1] D)
          (mapPost-isEquiv identityArrow groupoid) (CoreOfFun.uncurrying-isEquiv [1] D))

      termination-test : IsEquiv (mapPre {D = D} (terminate T))
      termination-test = equiv-cancel-left (mapPre (terminate T)) (mapPre l) localization-test
        (equiv-transport ((mapPre-cong (terminal-iso (terminate T ∘ l) (terminate [1])) ∙
          mapPre-comp l (terminate T)) ⁻¹) constant-test)

  abstract
    groupoid-isContractible : IsGroupoid T → IsContractible T
    groupoid-isContractible groupoid = pre-tests-isEquiv (terminate T)
      (Tested.termination-test T groupoid) (Tested.termination-test One terminal-isGroupoid)
```