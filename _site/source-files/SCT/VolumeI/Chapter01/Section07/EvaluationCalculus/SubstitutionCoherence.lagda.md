# Uncurrying and successive substitutions

This completes the iterated-precomposition clause of the book's finite
compatibility lemma. The product-substitution associativity witness is now
proved, so the evaluation transfer has no remaining hypothesis.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section07.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IteratedCompatibility as IteratedCompatibility
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity as ProductAssociativity

import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.SubstitutionCoherence
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯 M ℱ

open IteratedCompatibility 𝒯 M ℱ using (module Iteration)
open ProductAssociativity 𝒯 M using (slice-comparison-assoc)

funUncurry-restrict-iterated : {W Y X C D : CAT}
  (f : MAP X (Fun C D)) (σ : MAP Y X) (τ : MAP W Y)
  → (Iteration.together f σ τ) =₂ (Iteration.successively f σ τ)
funUncurry-restrict-iterated {C = C} f σ τ = Iteration.transfer f σ τ
  (slice-comparison-assoc C f σ τ)
```

`together` first applies the external associator and then substitutes
`σ ∘ τ`. `successively` substitutes `τ` and `σ` separately, then applies
the external associator and the chosen product-composition comparison.
Both routes retain the original uncurrying action on isomorphism animae.

