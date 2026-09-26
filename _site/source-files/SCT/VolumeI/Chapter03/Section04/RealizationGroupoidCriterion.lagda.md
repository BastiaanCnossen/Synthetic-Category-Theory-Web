# Why the realization is a groupoid

This is `(7) ⇒ (1)` in
`prop:Equivalent_Conditions_Geometric_Realization`. The localization
factors through the subcategory of isomorphisms in its target. If that
subcategory is the core, it therefore factors through the core. This
factor still inverts all source arrows, so extends across the
localization. Uniqueness after restriction makes the extension a section
of the core inclusion. That inclusion is an embedding, hence an
equivalence.

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

module SCT.VolumeI.Chapter03.Section04.RealizationGroupoidCriterion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (N : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; coreInclusion; core-isAn)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (embedding-with-section)
open import SCT.VolumeI.Chapter02.Section04.BasicClosure 𝒯 M ℱ P I E R
  using (IsGroupoid; equivalence-preserves-groupoid)
open Recognition.RecognitionAxiom N using (anima-isGroupoid)
open import SCT.VolumeI.Chapter02.Section05.PullbackAnimae 𝒯 M ℱ P I E S Q R N using (coreInclusion-isEmbedding)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (allMorphisms)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q
  using (isomorphisms; isomorphismInclusion)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S
  using (SubcategoryAxiom; SubcategoryPresentation)
open import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences 𝒯 M ℱ P I E S using (module Presented)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (Inverts)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingGroupoids 𝒯 M ℱ P I E S Q R using (isomorphisms-of-groupoid)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.LocalizationUniversal 𝒯 M ℱ P I E S Q R using (module Universal)

module FromCore (L : SubcategoryAxiom) {C T : CAT} (l : MAP C T)
  (localization : WithSubcategories.IsLocalization L (allMorphisms C) l)
  (A : SubcategoryPresentation (isomorphisms T))
  (h : MAP (Core T) (SubcategoryPresentation.subcategory A)) (equivalent : IsEquiv h)
  (over : (SubcategoryPresentation.inclusion A ∘ h) =₁ coreInclusion T) where
  open WithSubcategories L using (IsLocalization)
  i = SubcategoryPresentation.inclusion A
  inverts : FunctorLift (isomorphismInclusion T) (mapPost {C = [1]} l)
  inverts = record
    { lift = FunctorLift.lift (IsLocalization.inverts localization)
    ; comparison = comp-unitʳ (mapPost l) ∙ FunctorLift.comparison (IsLocalization.inverts localization) }
  module Factor = Presented.Factor (isomorphisms T) A l inverts using (factor; comparison)
  chosen = equiv-lift equivalent Factor.factor

  core-factor : MAP C (Core T)
  core-factor = FunctorLift.lift chosen

  core-factor-over : (coreInclusion T ∘ core-factor) =₁ l
  core-factor-over = Factor.comparison ∙
    ((i ◁ FunctorLift.comparison chosen) ∙
      (comp-assoc core-factor h i ∙ (over ⁻¹ ▷ core-factor)))

  core-factor-inverts : Inverts core-factor (allMorphisms C)
  core-factor-inverts = equiv-lift
    (isomorphisms-of-groupoid (Core T) (anima-isGroupoid (core-isAn T)))
    (mapPost core-factor ∘ id (Map [1] C))
  module UP = Universal L (allMorphisms C) l localization using (module Factor; restriction-reflects)
  module Extension = UP.Factor core-factor core-factor-inverts using (factor; comparison)

  section : MAP T (Core T)
  section = Extension.factor

  section-law : (coreInclusion T ∘ section) =₁ id T
  section-law = UP.restriction-reflects _ _
    ((comp-unitˡ l) ⁻¹ ∙
      (core-factor-over ∙
        ((coreInclusion T ◁ Extension.comparison) ∙ comp-assoc l section (coreInclusion T))))

  abstract
    core-inclusion-isEquiv : IsEquiv (coreInclusion T)
    core-inclusion-isEquiv = embedding-with-section (coreInclusion T)
      (coreInclusion-isEmbedding T) section section-law

    realization-isGroupoid : IsGroupoid T
    realization-isGroupoid = equivalence-preserves-groupoid (coreInclusion T)
      core-inclusion-isEquiv (anima-isGroupoid (core-isAn T))
```
