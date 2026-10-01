# The preceding axioms in every anima context

The basic theory and the mapping, pullback, and functor-category
structures are supplied by `Contexts` and `Theory`. This record supplies
the remaining primitive axiom packages of Chapters 1, 2, and 3 in each
ambient context. These are primitive local instances, including after
further anima extensions.

The availability of a local axiom package is distinct from preservation
of its chosen structure by a change of context. The latter requires
comparison data and is not asserted by this record.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Contexts
import SCT.VolumeI.Chapter05.Section01.Changes as Changes
import SCT.VolumeI.Chapter05.Theory as ContextTheory
import SCT.VolumeI.Chapter01.Section05.Initial as Initial
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universal
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section01.IntervalCore as IntervalCore
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition
import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom as Subcategories
import SCT.VolumeI.Chapter03.Section03.Localizations as Localizations
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Joins

module SCT.VolumeI.Chapter05.Axioms
  {l : Level} (C : ContextualTheories l) (D : Changes.Changes C)
  (K : ContextTheory.ContextualConstructions C D) where

open ContextualTheories C
open ContextTheory.ContextualConstructions K

record AxiomsInContext : Set l where
  field
    initial : (Γ : Context) → Initial.InitialStructure (at Γ) (mapping Γ)
    strict-initial : (Γ : Context) → Initial.StrictInitial (at Γ) (mapping Γ) (initial Γ)
    coproducts : (Γ : Context) → Coproducts.CoproductStructure (at Γ) (mapping Γ)
    universal-coproducts : (Γ : Context)
      → Universal.CoproductUniversality (at Γ) (mapping Γ) (coproducts Γ) (pullbacks Γ)
    interval : (Γ : Context) → Walking.WalkingMorphism (at Γ)
    endpoints : (Γ : Context)
      → Endpoints.IntervalEndpoints (at Γ) (mapping Γ) (functors Γ) (pullbacks Γ) (interval Γ)
    interval-core : (Γ : Context)
      → IntervalCore.IntervalCoreAxiom (at Γ) (mapping Γ) (coproducts Γ) (interval Γ)
    squares : (Γ : Context)
      → Squares.CommutativeSquareAxiom (at Γ) (mapping Γ) (functors Γ) (pullbacks Γ) (interval Γ) (endpoints Γ)
    segal : (Γ : Context)
      → Segal.SegalAxiom (at Γ) (mapping Γ) (functors Γ) (pullbacks Γ) (interval Γ) (endpoints Γ)
    rezk : (Γ : Context)
      → Rezk.RezkAxiom (at Γ) (mapping Γ) (functors Γ) (pullbacks Γ) (interval Γ) (endpoints Γ)
    recognition : (Γ : Context)
      → Recognition.RecognitionAxiom (at Γ) (mapping Γ) (functors Γ) (pullbacks Γ)
        (interval Γ) (endpoints Γ) (rezk Γ)
    subcategories : (Γ : Context)
      → Subcategories.SubcategoryAxiom (at Γ) (mapping Γ) (functors Γ) (pullbacks Γ)
        (interval Γ) (endpoints Γ) (segal Γ)
    localizations : (Γ : Context)
      → Localizations.WithSubcategories.LocalizationAxiom (at Γ) (mapping Γ) (functors Γ) (pullbacks Γ)
        (interval Γ) (endpoints Γ) (segal Γ) (squares Γ) (rezk Γ) (subcategories Γ)
    joins : (Γ : Context)
      → Joins.JoinAxiom (at Γ) (mapping Γ) (functors Γ) (coproducts Γ) (pullbacks Γ)
        (universal-coproducts Γ) (interval Γ)
```
