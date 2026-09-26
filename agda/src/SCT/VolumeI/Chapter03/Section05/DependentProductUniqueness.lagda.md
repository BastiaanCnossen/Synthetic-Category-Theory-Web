# Uniqueness from native relative currying

Transpose each evaluation into the other proposed dependent product.
Uncurrying the two composites reduces them to the original evaluations,
using composition and identity for base change. Reflection through
relative currying identifies the composites with the identities.

The final `Uniqueness` module applies this argument to the proved
computation of the specified uncurrying maps. Its forward equivalence
retains both the triangle over the base and the evaluation comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.DependentProductUniqueness
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)

module FromComputations {S T C : CAT} (p : MAP S T) (f : MAP C S)
  (Π Ψ : DependentProduct p f)
  (computationΠ : Currying.Computation p f Π) (computationΨ : Currying.Computation p f Ψ) where
  module Left = Currying.FromComputation p f Π computationΠ
  module Right = Currying.FromComputation p f Ψ computationΨ
  g : MAP (DependentProduct.category Π) T
  g = DependentProduct.projection Π
  h : MAP (DependentProduct.category Ψ) T
  h = DependentProduct.projection Ψ

  forward : FunctorOver g h
  forward = Right.factor g (DependentProduct.evaluation Π)
  backward : FunctorOver h g
  backward = Left.factor h (DependentProduct.evaluation Ψ)

  abstract
    forward-evaluation : FunctorOverIso (Currying.evaluate p f Ψ forward) (DependentProduct.evaluation Π)
    forward-evaluation = Right.factor-β g (DependentProduct.evaluation Π)

    backward-evaluation : FunctorOverIso (Currying.evaluate p f Π backward) (DependentProduct.evaluation Ψ)
    backward-evaluation = Left.factor-β h (DependentProduct.evaluation Ψ)

    left-inverse : FunctorOverIso (compose-over backward forward) (identity-over g)
    left-inverse = Left.reflect g (compose-over backward forward) (identity-over g)
      (compose-iso-over (inverse-iso-over Left.evaluate-identity)
        (compose-iso-over forward-evaluation
          (compose-iso-over (prewhisker-over (Change.functor p forward) backward-evaluation)
            (Left.evaluate-composite forward backward))))

    right-inverse : FunctorOverIso (compose-over forward backward) (identity-over h)
    right-inverse = Right.reflect h (compose-over forward backward) (identity-over h)
      (compose-iso-over (inverse-iso-over Right.evaluate-identity)
        (compose-iso-over backward-evaluation
          (compose-iso-over (prewhisker-over (Change.functor p backward) forward-evaluation)
            (Right.evaluate-composite backward forward))))

    forward-isEquiv : IsEquiv (FunctorLift.lift forward)
    forward-isEquiv = record
      { inverse = FunctorLift.lift backward
      ; sectionIso = (FunctorOverIso.underlying left-inverse) ⁻¹
      ; retractionIso = (FunctorOverIso.underlying right-inverse) ⁻¹ }
module Uniqueness {S T C : CAT} (p : MAP S T) (f : MAP C S)
  (Π Ψ : DependentProduct p f) where
  open FromComputations p f Π Ψ (Currying.named-computation p f Π)
    (Currying.named-computation p f Ψ) public
```
