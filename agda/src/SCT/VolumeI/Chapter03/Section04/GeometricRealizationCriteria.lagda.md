# The seven equivalent conditions for geometric realization

This is the implication cycle in
`prop:Equivalent_Conditions_Geometric_Realization`. The named conditions
follow the manuscript's order. The arrows below prove the cycle and the
additional equivalence between fullness of constant diagrams and fullness
of isomorphisms. None calls the unconditional fundamental groupoid theorem.

The proofs they assemble occur in the supporting modules: contractibility
is tested on mapping animae, fullness is transported through localization,
and the subcategory of isomorphisms is compared with the core. The later
`FundamentalGroupoids` module establishes the conditions without hypotheses.

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

module SCT.VolumeI.Chapter03.Section04.GeometricRealizationCriteria
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (N : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; coreInclusion)
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I using (identityArrow)
open Rezk 𝒯 M ℱ P I E using (isoArrow)
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
open Recognition.RecognitionAxiom N using (groupoid-isAn)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S
  using (SubcategoryAxiom; SubcategoryPresentation)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q
  using (isomorphisms; constantMap)
open import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.IsomorphismClosure 𝒯 M ℱ P I E S Q R N using (isomorphisms-closed)
open import SCT.VolumeI.Chapter03.Section01.Subcategories 𝒯 M P I using (IsSubcategory)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P using (IsFullSubcategory)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section04.GeometricRealization 𝒯 M ℱ P I E S Q R using (module Realization)
open import SCT.VolumeI.Chapter03.Section04.RealizationOfInterval 𝒯 M ℱ P I E S Q R using (module Interval)
open import SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.ConstantFullSubcategory 𝒯 M ℱ P I E S Q R using (module FromContractible)
open import SCT.VolumeI.Chapter03.Section04.GroupoidCriterion 𝒯 M ℱ P I E S Q R
  using (morphismwise-groupoid-criterion; isomorphism-full-from-constant-full; constant-full-from-isomorphism-full)
open import SCT.VolumeI.Chapter03.Section04.IsomorphismSubcategoryCore 𝒯 M ℱ P I E S Q R N using (module CoreComparison)
open import SCT.VolumeI.Chapter03.Section04.RealizationGroupoidCriterion 𝒯 M ℱ P I E S Q R N using (module FromCore)

open import SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.GroupoidRealizationInterval 𝒯 M ℱ P I E S Q R
  using () renaming (module Interval to GroupoidInterval)

module Criteria (L : SubcategoryAxiom) (Z : WithSubcategories.LocalizationAxiom L) where
  module Geom = Realization L Z using (category; localization; universal)

  module Selected (C : CAT) where
    abstract
      presentation : SubcategoryPresentation (isomorphisms C)
      presentation = SubcategoryAxiom.generated L (isomorphisms C) (isomorphisms-closed C)
    category = SubcategoryPresentation.subcategory presentation
    module CoreData = CoreComparison C presentation
      using (from-core; from-core-over-C; constantMap-isEquiv; module IfGroupoid)

  RealizationsAreGroupoids = (C : CAT) → IsGroupoid (Geom.category C)
  IntervalRealizationIsContractible = IsContractible (Geom.category [1])
  ConstantDiagramsAreFull = (C : CAT) → IsFullSubcategory (identityArrow {C})
  IsomorphismsAreFull = (C : CAT) → IsFullSubcategory (isoArrow {C})
  GroupoidsAreDetectedOnArrows = (C : CAT) → IsEquiv (constantMap C) → IsGroupoid C
  IsomorphismSubcategoriesAreGroupoids = (C : CAT) → IsGroupoid (Selected.category C)
  CoresAreIsomorphismSubcategories = (C : CAT) → IsEquiv (Selected.CoreData.from-core C)

  abstract
    groupoids-to-contractible-interval : RealizationsAreGroupoids → IntervalRealizationIsContractible
    groupoids-to-contractible-interval all = GroupoidInterval.groupoid-isContractible L
      (Geom.category [1]) (Geom.localization [1]) (Geom.universal [1]) (all [1])

    contractible-interval-to-full-constants : IntervalRealizationIsContractible → ConstantDiagramsAreFull
    contractible-interval-to-full-constants = FromContractible.At.identityArrow-isFullSubcategory L
      (Geom.category [1]) (Geom.localization [1]) (Geom.universal [1])

    full-constants-to-full-isomorphisms : ConstantDiagramsAreFull → IsomorphismsAreFull
    full-constants-to-full-isomorphisms full C = isomorphism-full-from-constant-full C (full C)

    full-isomorphisms-to-full-constants : IsomorphismsAreFull → ConstantDiagramsAreFull
    full-isomorphisms-to-full-constants full C = constant-full-from-isomorphism-full C (full C)

    full-constants-to-arrow-detection : ConstantDiagramsAreFull → GroupoidsAreDetectedOnArrows
    full-constants-to-arrow-detection full C = morphismwise-groupoid-criterion C (full C)

    arrow-detection-to-groupoid-subcategories : GroupoidsAreDetectedOnArrows → IsomorphismSubcategoriesAreGroupoids
    arrow-detection-to-groupoid-subcategories detect C =
      detect (Selected.category C) (Selected.CoreData.constantMap-isEquiv C)

    groupoid-subcategories-to-cores : IsomorphismSubcategoriesAreGroupoids → CoresAreIsomorphismSubcategories
    groupoid-subcategories-to-cores groupoids C =
      Selected.CoreData.IfGroupoid.from-core-isEquiv C (groupoid-isAn (groupoids C))

    cores-to-groupoid-realizations : CoresAreIsomorphismSubcategories → RealizationsAreGroupoids
    cores-to-groupoid-realizations cores C = FromCore.realization-isGroupoid L
      (Geom.localization C) (Geom.universal C) (Selected.presentation (Geom.category C))
      (Selected.CoreData.from-core (Geom.category C)) (cores (Geom.category C))
      (Selected.CoreData.from-core-over-C (Geom.category C))
```
