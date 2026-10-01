# Further axiom comparisons in context

The initial-category and coproduct universal properties are compared with
their selected witnesses, in every change of ambient context. Strictness
receives the same treatment for every functor into the initial category.
The interval comparison here includes its two endpoints.

This record is a component of the preservation scheme. It does not yet
record the comparisons for universal coproducts, the other interval
axioms, subcategories, localizations, or joins.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Contexts
import SCT.VolumeI.Chapter05.Section01.Changes as Changes
import SCT.VolumeI.Chapter05.Theory as ContextTheory
import SCT.VolumeI.Chapter05.Axioms as Axioms
import SCT.VolumeI.Chapter05.Preservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ConstructorCertificates as Certificates
import SCT.VolumeI.Chapter05.Section01.IntervalPreservation as Interval

module SCT.VolumeI.Chapter05.AxiomPreservation
  {l : Level} (C : ContextualTheories l) (D : Changes.Changes C)
  (K : ContextTheory.ContextualConstructions C D) (L : Changes.LiftComparisons C D)
  (P : Preservation.Preservation C D K L) (AX : Axioms.AxiomsInContext C D K) where

open ContextualTheories C
open Changes.Changes D
open ContextTheory.ContextualConstructions K
open Axioms.AxiomsInContext AX
open Preservation.Preservation P
open Preservation C D K L using (products)

module At {Γ Δ : Context} (w : Change Γ Δ) where
  module Initial = Certificates.InitialComparison (underlying {Γ} {Δ} w) (products {Γ} {Δ} w)
    (mapping Γ) (mapping Δ) (mapping-animae {Γ} {Δ} w) (initial Γ) (initial Δ)
    using (Comparison; Strictness)
  module Coproduct = Certificates.CoproductComparison (underlying {Γ} {Δ} w) (products {Γ} {Δ} w)
    (mapping Γ) (mapping Δ) (mapping-animae {Γ} {Δ} w) (coproducts Γ) (coproducts Δ)
    using (Comparison)

record Comparisons : Set l where
  field
    initial-categories : {Γ Δ : Context} (w : Change Γ Δ) → At.Initial.Comparison {Γ} {Δ} w
    strict-initial-certificates : {Γ Δ : Context} (w : Change Γ Δ)
      → At.Initial.Strictness {Γ} {Δ} w (initial-categories {Γ} {Δ} w) (strict-initial Γ) (strict-initial Δ)
    coproduct-categories : {Γ Δ : Context} (w : Change Γ Δ) → At.Coproduct.Comparison {Γ} {Δ} w
    intervals : {Γ Δ : Context} (w : Change Γ Δ)
      → Interval.Comparison (underlying {Γ} {Δ} w) (interval Γ) (interval Δ)
```
