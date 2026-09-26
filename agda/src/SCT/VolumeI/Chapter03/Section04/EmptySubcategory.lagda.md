# The empty subcategory

The empty example in Section 3.1 follows from the morphismwise groupoid
criterion. Span the empty collection of objects in `C`. Its core maps
to `Zero`, so `EmptyCore` identifies this spanned subcategory with
`Zero`. Transfer the subcategory and full-subcategory properties along
that equivalence. Initiality identifies the transferred inclusion with
the chosen functor `initiate C`.

This supporting module takes the criterion as a proved input. The
unconditional specialization is exported with the geometric-realization
theorems, so the example introduces no new axiom.

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

module SCT.VolumeI.Chapter03.Section04.EmptySubcategory
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (N : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R)
  (Z : Initial.InitialStructure 𝒯 M) (strict : Initial.StrictInitial 𝒯 M Z) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Initial.Initiality 𝒯 M Z
open Initial.StrictInitial strict
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (projection-embedding)
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
open Recognition.Consequences 𝒯 M ℱ P I E R N using (zero-isAn)
open import SCT.VolumeI.Chapter03.Section01.Subcategories 𝒯 M P I using (IsSubcategory)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryEquivalences 𝒯 M P I
  using (subcategory-precompose-equivalence)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q using (constantMap)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences 𝒯 M ℱ P I E S using (module Presented)
open import SCT.VolumeI.Chapter03.Section02.ObjectCollections 𝒯 M P I using (ObjectCollection)
open import SCT.VolumeI.Chapter03.Section02.SpannedSubcategories 𝒯 M ℱ P I E S using (module Spanned)
open import SCT.VolumeI.Chapter03.Section02.SpannedCore 𝒯 M ℱ P I E S using (module CoreComparison)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P using (IsFullSubcategory)
open import SCT.VolumeI.Chapter03.Section02.Factorization.FullSubcategoryEquivalences 𝒯 M P
  using (full-subcategory-precompose-equivalence)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategoryCharacterization 𝒯 M ℱ P I E S using (module Characterization)
open import SCT.VolumeI.Chapter03.Section04.EmptyCore 𝒯 M ℱ P I E S Q R N Z strict using (module Detection)

emptyObjects : (C : CAT) → ObjectCollection C
emptyObjects C = record
  { collection = Zero ; collection-isAn = zero-isAn Z strict
  ; inclusion = initiate (Core C)
  ; inclusion-isEmbedding = projection-embedding (initiate (Core C)) (into-zero-isEquiv pullback₁) }

module FromCriterion (L : SubcategoryAxiom)
  (detect : (C : CAT) → IsEquiv (constantMap C) → IsGroupoid C) (C : CAT) where
  module Empty = Spanned L (emptyObjects C) using (category; inclusion; presentation)
  module Core = CoreComparison (emptyObjects C) Empty.presentation using (comparison)
  module Initiality = Detection detect Empty.category Core.comparison using (initial-isEquiv)

  abstract
    empty-isSubcategory : IsSubcategory (initiate C)
    empty-isSubcategory = subcategory-precompose-equivalence (initiate C) Empty.inclusion
      (initiate Empty.category) Initiality.initial-isEquiv (initial-iso _ _)
      (Presented.inclusion-isSubcategory _ Empty.presentation)

    empty-isFullSubcategory : IsFullSubcategory (initiate C)
    empty-isFullSubcategory = full-subcategory-precompose-equivalence (initiate C) Empty.inclusion
      (initiate Empty.category) Initiality.initial-isEquiv (initial-iso _ _)
      (Characterization.isFullSubcategory (emptyObjects C) Empty.presentation)
```
