# The realization of the walking morphism is contractible

This is the implication proved in `axiom:N_Fundamental_Groupoid_Axiom`.
For every target, restriction identifies maps out of the realization
with functors that invert all arrows. `InvertingInterval` identifies
these with constant functors, compatibly with their inclusions into
the mapping anima. Thus the terminal projection of the realization
induces an equivalence on mapping animae, and is an equivalence.

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

module SCT.VolumeI.Chapter03.Section04.RealizationOfInterval
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (pre-tests-all)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (embedding-reflect)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (allMorphisms)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationMappingProperty 𝒯 M ℱ P I E S Q R
  using (MappingUniversalProperty; mapping-universal-property)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)
open import SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.InvertingInterval 𝒯 M ℱ P I E S Q R using (module Into)

module Interval (L : SubcategoryAxiom) (T : CAT) (l : MAP [1] T)
  (localization : WithSubcategories.IsLocalization L (allMorphisms [1]) l) where
  property : MappingUniversalProperty (allMorphisms [1]) l
  property = mapping-universal-property L {C = [1]} {T = T} (allMorphisms [1]) l localization

  module Tested (D : CAT) where
    inclusion = Inverting.inclusion (allMorphisms [1]) D
    constants = Into.constants D

    restriction = MappingUniversalProperty.restriction property D
    comparison = MappingUniversalProperty.comparison property D

    triangle : (restriction ∘ mapPre (terminate T)) =₁ constants
    triangle = embedding-reflect inclusion (Inverting.inclusion-isEmbedding (allMorphisms [1]) D) _ _
      (Into.constants-comparison D ⁻¹ ∙
        (mapPre-cong {D = D} (terminal-iso (terminate T ∘ l) (terminate [1])) ∙
          (mapPre-comp l (terminate T) ∙
            ((comparison ▷ mapPre (terminate T)) ∙
              (comp-assoc (mapPre (terminate T)) restriction inclusion) ⁻¹))))

    restriction-isEquiv : IsEquiv (mapPre {D = D} (terminate T))
    restriction-isEquiv = equiv-cancel-left (mapPre {D = D} (terminate T)) restriction
      (MappingUniversalProperty.isEquiv property D)
      (equiv-transport (triangle ⁻¹) (Into.constants-isEquiv D))

  abstract
    realization-interval-contractible : IsContractible T
    realization-interval-contractible = pre-tests-all (terminate T) Tested.restriction-isEquiv
```
