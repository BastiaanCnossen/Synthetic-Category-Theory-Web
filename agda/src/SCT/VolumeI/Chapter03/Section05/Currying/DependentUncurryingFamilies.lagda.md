# Uncurrying on arbitrary category parameters

Evaluation of a relative family commutes with dependent-product
uncurrying. The parameterized pullback cone retains the base triangle;
its universal lift compares the chosen pullback with the product of the
parameter and the original pullback.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.DependentUncurryingFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
import SCT.VolumeI.Chapter03.Section05.Currying.RelativeEvaluationFamilies as Families

module Evaluation {S T C K : CAT} (p : MAP S T) (f : MAP C S)
  (Π : DependentProduct p f) (k : MAP K T) where
  g = DependentProduct.projection Π
  ε = DependentProduct.evaluation Π
  module Raw = Families.Evaluation 𝒯 M ℱ P p f g ε k using (functor; module At)
  open Raw public using (functor)
  module Native = Currying p f Π using (evaluate)
  k′ : MAP (Pullback k p) S
  k′ = pullback₂
  module At (X : CAT) where
    module RawAt = Raw.At X using (inclusion; inclusion-isEquiv; family-comparison)
    open RawAt public using (inclusion; inclusion-isEquiv)
    abstract
      family-comparison : (F : MAP X (FunOver k g)) → FunctorOverIso
        (family k′ f (functor ∘ F))
        (compose-over (Native.evaluate (family k g F)) inclusion)
      family-comparison = RawAt.family-comparison
```
