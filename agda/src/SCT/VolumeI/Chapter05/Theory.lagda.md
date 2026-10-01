# Contextual structures used in Chapter 5

The structures below are supplied at every ambient context. Thus the
dependent product and sum rules can be applied again after any finite
number of anima extensions. The basic change data, constructor
preservation data, and substitution data remain separate interfaces.

This record gathers the constructors used below. It is not a replacement
for the additional axiom records of Chapters 2 and 3, which can likewise
be supplied at each context.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Contexts
import SCT.VolumeI.Chapter05.Section01.Changes as Changes
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section03.Recovery as Recovery

module SCT.VolumeI.Chapter05.Theory
  {l : Level} (C : ContextualTheories l) (D : Changes.Changes C) where

open ContextualTheories C
open Changes.Changes D using (underlying; weakening)

W : (Γ : Context) (A : In.AN Γ) → Weakening (at Γ) (Local Γ A)
W Γ A = underlying (weakening Γ A)

record ContextualConstructions : Set l where
  field
    mapping : (Γ : Context) → Mapping.MappingAnimae (at Γ)
    pullbacks : (Γ : Context) → Pullbacks.PullbackStructure (at Γ)
    functors : (Γ : Context) → Functors.FunctorCategories (at Γ) (mapping Γ)
    dependentProducts : (Γ : Context) (A : In.AN Γ) → Products.DependentProducts (W Γ A)
    dependentSums : (Γ : Context) (A : In.AN Γ)
      → Sums.DependentSums (W Γ A) (dependentProducts Γ A)

  module Π (Γ : Context) (A : In.AN Γ) = Products.DependentProducts (dependentProducts Γ A)
  module Σ (Γ : Context) (A : In.AN Γ) = Sums.DependentSums (dependentSums Γ A)

  field
    terminalSum : (Γ : Context) (A : In.AN Γ)
      → In.Equiv Γ (Σ.Σ Γ A (In.One (extend Γ A))) (In.AN.category {Γ = Γ} A)
    recovery : (Γ : Context) (A : In.AN Γ)
      → Recovery.Recovery (W Γ A) (dependentProducts Γ A) (dependentSums Γ A) A (terminalSum Γ A)
        (Pullbacks.PullbackStructure.dataPullback (pullbacks (extend Γ A)))
```
