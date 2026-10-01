# Constructor comparisons in every ambient context

Every field is indexed by a change code. In particular it applies to a
weakening, a substitution supplied as a change, and every iterated lift.
The dependent universal-property certificates use the recursive
comparison of identification animae from `ComparisonWitnesses`.

This is the preservation interface for the constructors recorded here.
The universal-certificate interfaces still accept a comparison square
for each compound universal-property functor. Agreement of that square
with the recursively generated expression comparison remains to be
proved. Consequently this record is a partial interface for the approved
preservation scheme, not its complete implementation.

Selected product and pullback universal-property certificates
also remain to be covered, as do the additional constructors of Chapters
2 and 3, the recovery certificates, and the higher witnesses of the
lifting comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Contexts
import SCT.VolumeI.Chapter05.Section01.Changes as Changes
import SCT.VolumeI.Chapter05.Theory as ContextTheory
open import SCT.VolumeI.Chapter05.Section01.PrimitivePreservation using (PrimitiveWeakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
open import SCT.VolumeI.Chapter05.Section01.Products using (PreservesProducts)
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Functors
import SCT.VolumeI.Chapter05.Section01.MappingPreservation as Mapping
import SCT.VolumeI.Chapter05.Section01.ConstructorCertificates as Certificates
import SCT.VolumeI.Chapter05.Section01.PullbackPreservation as Pullbacks
import SCT.VolumeI.Chapter05.Section01.TerminalPreservation as Terminal
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as PullbackLaws
import SCT.VolumeI.Chapter05.Section04.DependentPreservation as Dependent
import SCT.VolumeI.Chapter05.Section04.ProductUniversalPreservation as ProductCertificates
import SCT.VolumeI.Chapter05.Section04.SumUniversalPreservation as SumCertificates
import SCT.VolumeI.Chapter05.Section04.TerminalSumPreservation as TerminalCertificates

module SCT.VolumeI.Chapter05.Preservation
  {l : Level} (C : ContextualTheories l) (D : Changes.Changes C)
  (K : ContextTheory.ContextualConstructions C D) (L : Changes.LiftComparisons C D) where

open ContextualTheories C
open Changes.Changes D
open Changes.LiftComparisons L
open ContextTheory C D using (W)
open ContextTheory.ContextualConstructions K

products : {Γ Δ : Context} (w : Change Γ Δ)
  → PreservesProducts (underlying {Γ} {Δ} w)
products {Γ} {Δ} w = OperationCompatibility.products (PrimitiveWeakening.operations (realization {Γ} {Δ} w))

module Lifted {Γ Δ : Context} (w : Change Γ Δ) (A : In.AN Γ) where
  module Data = Dependent (W Γ A) (W Δ (image-anima {Γ} {Δ} w A))
    (underlying {Γ} {Δ} w) (underlying (lift {Γ} {Δ} w A)) (weakening-comparison {Γ} {Δ} w A)
    (dependentProducts Γ A) (dependentProducts Δ (image-anima {Γ} {Δ} w A))
    using (ProductComparison; ProductComputations)
  module Sum = Dependent.Sum (W Γ A) (W Δ (image-anima {Γ} {Δ} w A))
    (underlying {Γ} {Δ} w) (underlying (lift {Γ} {Δ} w A)) (weakening-comparison {Γ} {Δ} w A)
    (dependentProducts Γ A) (dependentProducts Δ (image-anima {Γ} {Δ} w A))
    (dependentSums Γ A) (dependentSums Δ (image-anima {Γ} {Δ} w A))
    using (SumComparison; SumComputations)
  module ProductUniversal = ProductCertificates (W Γ A) (W Δ (image-anima {Γ} {Δ} w A))
    (underlying {Γ} {Δ} w) (underlying (lift {Γ} {Δ} w A)) (products {Γ} {Δ} w) (products (lift {Γ} {Δ} w A))
    (weakening-comparison {Γ} {Δ} w A) (dependentProducts Γ A) (dependentProducts Δ (image-anima {Γ} {Δ} w A)) using (Comparison)
  module SumUniversal = SumCertificates (W Γ A) (W Δ (image-anima {Γ} {Δ} w A))
    (underlying {Γ} {Δ} w) (underlying (lift {Γ} {Δ} w A)) (products {Γ} {Δ} w) (products (lift {Γ} {Δ} w A))
    (weakening-comparison {Γ} {Δ} w A) (dependentProducts Γ A) (dependentProducts Δ (image-anima {Γ} {Δ} w A))
    (dependentSums Γ A) (dependentSums Δ (image-anima {Γ} {Δ} w A)) using (Comparison)
  module TerminalUniversal (S : Sum.SumComparison) = TerminalCertificates
    (W Γ A) (W Δ (image-anima {Γ} {Δ} w A)) (underlying {Γ} {Δ} w) (underlying (lift {Γ} {Δ} w A)) (products {Γ} {Δ} w)
    (weakening-comparison {Γ} {Δ} w A) (dependentProducts Γ A) (dependentProducts Δ (image-anima {Γ} {Δ} w A))
    (dependentSums Γ A) (dependentSums Δ (image-anima {Γ} {Δ} w A)) S A
    (terminalSum Γ A) (terminalSum Δ (image-anima {Γ} {Δ} w A)) using (Comparison)

record Preservation : Set l where
  field
    terminal-certificates : {Γ Δ : Context} (w : Change Γ Δ)
      → Terminal.Comparison (underlying {Γ} {Δ} w) (products {Γ} {Δ} w)
    mapping-animae : {Γ Δ : Context} (w : Change Γ Δ)
      → Mapping.MappingComparison (underlying {Γ} {Δ} w) (products {Γ} {Δ} w) (mapping Γ) (mapping Δ)
    mapping-computations : {Γ Δ : Context} (w : Change Γ Δ)
      → Mapping.Comparisons.Computation (underlying {Γ} {Δ} w) (products {Γ} {Δ} w) (mapping Γ) (mapping Δ)
        (mapping-animae {Γ} {Δ} w)
    mapping-certificates : {Γ Δ : Context} (w : Change Γ Δ)
      → Mapping.Comparisons.Universal (underlying {Γ} {Δ} w) (products {Γ} {Δ} w) (mapping Γ) (mapping Δ)
        (mapping-animae {Γ} {Δ} w)
    functor-categories : {Γ Δ : Context} (w : Change Γ Δ)
      → Functors.FunctorComparison (underlying {Γ} {Δ} w) (mapping Γ) (mapping Δ)
        (ContextTheory.ContextualConstructions.functors K Γ) (ContextTheory.ContextualConstructions.functors K Δ)
    functor-certificates : {Γ Δ : Context} (w : Change Γ Δ)
      → Certificates.FunctorComparison.Universal (underlying {Γ} {Δ} w) (products {Γ} {Δ} w) (mapping Γ) (mapping Δ)
        (mapping-animae {Γ} {Δ} w) (ContextTheory.ContextualConstructions.functors K Γ)
        (ContextTheory.ContextualConstructions.functors K Δ) (functor-categories {Γ} {Δ} w)
    pullback-categories : {Γ Δ : Context} (w : Change Γ Δ)
      → Pullbacks.PreservesPullbacks (underlying {Γ} {Δ} w)
        (PullbackLaws.PullbackStructure.dataPullback (ContextTheory.ContextualConstructions.pullbacks K Γ))
        (PullbackLaws.PullbackStructure.dataPullback (ContextTheory.ContextualConstructions.pullbacks K Δ))
    dependent-products : {Γ Δ : Context} (w : Change Γ Δ) (A : In.AN Γ)
      → Lifted.Data.ProductComparison {Γ} {Δ} w A
    dependent-product-computations : {Γ Δ : Context} (w : Change Γ Δ) (A : In.AN Γ)
      → Lifted.Data.ProductComputations {Γ} {Δ} w A (dependent-products {Γ} {Δ} w A)
    dependent-product-certificates : {Γ Δ : Context} (w : Change Γ Δ) (A : In.AN Γ)
      → Lifted.ProductUniversal.Comparison {Γ} {Δ} w A (dependent-products {Γ} {Δ} w A)
    dependent-sums : {Γ Δ : Context} (w : Change Γ Δ) (A : In.AN Γ)
      → Lifted.Sum.SumComparison {Γ} {Δ} w A
    dependent-sum-computations : {Γ Δ : Context} (w : Change Γ Δ) (A : In.AN Γ)
      → Lifted.Sum.SumComputations {Γ} {Δ} w A (dependent-sums {Γ} {Δ} w A)
    dependent-sum-certificates : {Γ Δ : Context} (w : Change Γ Δ) (A : In.AN Γ)
      → Lifted.SumUniversal.Comparison {Γ} {Δ} w A (dependent-products {Γ} {Δ} w A) (dependent-sums {Γ} {Δ} w A)
    terminal-sum-certificates : {Γ Δ : Context} (w : Change Γ Δ) (A : In.AN Γ)
      → Lifted.TerminalUniversal.Comparison {Γ} {Δ} w A (dependent-sums {Γ} {Δ} w A)
```
