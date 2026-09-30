# Uncurrying the specified relative point

The categorical uncurrying functor sends a named relative functor to
its native evaluation. Use its comparison on cores, the named native
computation, and naturality of the core inclusion. The point still
contains the supplied triangle over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.DependentUncurryingPoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M using (coreInclusion; coreInclusion-natural)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeEvaluationFamilies 𝒯 M ℱ P using (module Evaluation)

relative-point : {C D S : CAT} (f : MAP C S) (g : MAP D S) → FunctorOver f g → Obj-abs (FunOver f g)
relative-point f g u = coreInclusion (FunOver f g) ∘ Over.name-over f g u

module Points {S T C K : CAT} (p : MAP S T) (f : MAP C S)
  (Π : DependentProduct p f) (k : MAP K T) where
  g = DependentProduct.projection Π
  ε = DependentProduct.evaluation Π
  k′ : MAP (Pullback k p) S
  k′ = pullback₂
  module Raw = Evaluation p f g ε k using (functor; mapping-comparison)
  module Native = Currying p f Π using (evaluate; named-computation)
  abstract
    comparison : (u : FunctorOver k g) →
      (Raw.functor ∘ relative-point k g u) =₁ relative-point k′ f (Native.evaluate u)
    comparison u =
      (coreInclusion (FunOver k′ f) ◁
        (Native.named-computation k u ∙ (Raw.mapping-comparison ⁻¹ ▷ Over.name-over k g u))) ∙
      (comp-assoc (Over.name-over k g u) (mapPost Raw.functor) (coreInclusion (FunOver k′ f)) ∙
        (((coreInclusion-natural Raw.functor) ⁻¹ ▷ Over.name-over k g u) ∙
          (comp-assoc (Over.name-over k g u) (coreInclusion (FunOver k g)) Raw.functor) ⁻¹))
```
