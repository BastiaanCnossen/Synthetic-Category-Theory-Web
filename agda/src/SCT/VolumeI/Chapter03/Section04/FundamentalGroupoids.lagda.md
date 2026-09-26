# The fundamental groupoid theorem

This assembles the seven conclusions of
`prop:Equivalent_Conditions_Geometric_Realization` and proves
`axiom:N_Fundamental_Groupoid_Axiom`, which is a proposition in the
manuscript. No geometric-realization axiom is added.

Start with the contractibility of the realized interval. Its universal
property makes constant arrows a full subcategory. Fullness detects
groupoids on the mapping anima of arrows. Apply this to the subcategory
of isomorphisms, identify it with the core, and factor a localization
through its core to see that every realization is a groupoid.

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

module SCT.VolumeI.Chapter03.Section04.FundamentalGroupoids
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
  using (morphismwise-groupoid-criterion; isomorphism-full-from-constant-full)
open import SCT.VolumeI.Chapter03.Section04.IsomorphismSubcategoryCore 𝒯 M ℱ P I E S Q R N using (module CoreComparison)
open import SCT.VolumeI.Chapter03.Section04.RealizationGroupoidCriterion 𝒯 M ℱ P I E S Q R N using (module FromCore)
import SCT.VolumeI.Chapter03.Section04.EmptySubcategory as Empty

module Consequences (L : SubcategoryAxiom) (Z : WithSubcategories.LocalizationAxiom L) where
  module Geom = Realization L Z using (category; localization; universal)

  abstract
    realization-interval-contractible : IsContractible (Geom.category [1])
    realization-interval-contractible = Interval.realization-interval-contractible L
      (Geom.category [1]) (Geom.localization [1]) (Geom.universal [1])

    identityArrow-isFullSubcategory : (C : CAT) → IsFullSubcategory (identityArrow {C})
    identityArrow-isFullSubcategory = FromContractible.At.identityArrow-isFullSubcategory L
      (Geom.category [1]) (Geom.localization [1]) (Geom.universal [1]) realization-interval-contractible

    isoArrow-isFullSubcategory : (C : CAT) → IsFullSubcategory (isoArrow {C})
    isoArrow-isFullSubcategory C = isomorphism-full-from-constant-full C (identityArrow-isFullSubcategory C)

    morphismwise-groupoid : (C : CAT) → IsEquiv (constantMap C) → IsGroupoid C
    morphismwise-groupoid C = morphismwise-groupoid-criterion C (identityArrow-isFullSubcategory C)

  module IsomorphismSubcategory (C : CAT) where
    abstract
      presentation : SubcategoryPresentation (isomorphisms C)
      presentation = SubcategoryAxiom.generated L (isomorphisms C) (isomorphisms-closed C)
    category = SubcategoryPresentation.subcategory presentation
    inclusion = SubcategoryPresentation.inclusion presentation
    module CoreData = CoreComparison C presentation
      using (from-core; from-core-over-C; constantMap-isEquiv; module IfGroupoid)

    abstract
      isGroupoid : IsGroupoid category
      isGroupoid = morphismwise-groupoid category CoreData.constantMap-isEquiv

    from-core : MAP (Core C) category
    from-core = CoreData.from-core

    from-core-over-C : (inclusion ∘ from-core) =₁ coreInclusion C
    from-core-over-C = CoreData.from-core-over-C

    abstract
      from-core-isEquiv : IsEquiv from-core
      from-core-isEquiv = CoreData.IfGroupoid.from-core-isEquiv (groupoid-isAn isGroupoid)

  abstract
    realization-isGroupoid : (C : CAT) → IsGroupoid (Geom.category C)
    realization-isGroupoid C = FromCore.realization-isGroupoid L (Geom.localization C) (Geom.universal C)
      (IsomorphismSubcategory.presentation (Geom.category C))
      (IsomorphismSubcategory.from-core (Geom.category C))
      (IsomorphismSubcategory.from-core-isEquiv (Geom.category C))
      (IsomorphismSubcategory.from-core-over-C (Geom.category C))

    realization-isAn : (C : CAT) → isAn (Geom.category C)
    realization-isAn C = groupoid-isAn (realization-isGroupoid C)
```

The empty example from Section 3.1 is now unconditional under the book's
axioms. Its proof uses the criterion above, explaining its placement
after the geometric-realization argument in the dependency graph.

```agda
  module WithInitial (O : Initial.InitialStructure 𝒯 M) (strict : Initial.StrictInitial 𝒯 M O) where
    open Initial.Initiality 𝒯 M O using (initiate)
    module Proof = Empty 𝒯 M ℱ P I E S Q R N O strict using (module FromCriterion)

    abstract
      empty-isSubcategory : (C : CAT) → IsSubcategory (initiate C)
      empty-isSubcategory = Proof.FromCriterion.empty-isSubcategory L morphismwise-groupoid

      empty-isFullSubcategory : (C : CAT) → IsFullSubcategory (initiate C)
      empty-isFullSubcategory = Proof.FromCriterion.empty-isFullSubcategory L morphismwise-groupoid
```
