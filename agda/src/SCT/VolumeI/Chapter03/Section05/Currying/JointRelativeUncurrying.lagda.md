# Joint source naturality of relative uncurrying

Uncurrying a composite agrees with first changing the base of its inner
functor and uncurrying its outer functor. Evaluate both sides on their
common parameter, use the base-change comparison for composite families,
and postcompose by evaluation. Lift this entire relative identification,
retaining its triangle computation.

The evaluation need not have a universal property. In particular, this
applies to the stipulated uncurrying functors of dependent products.
Restriction naturality concerns this whole chosen comparison; agreement
with earlier pointwise native comparisons is a separate computation.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.RelativeCategories.Families.CoherentRelativeFamilyLifting as CoherentLifting

module SCT.VolumeI.Chapter03.Section05.Currying.JointRelativeUncurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
  using (family; family-identification; postcompose-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.RetainedRelativeFamilies 𝒯 M ℱ P using (module Identification)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeSubstitution 𝒯 M ℱ P using (module Substitution)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.JointComposition 𝒯 M ℱ P using (module Joint)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeEvaluationFamilies 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.JointBaseChangeCompositor 𝒯 M ℱ P using (module Compositor)

module Natural {K L C D S T : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D T)
  (ε : FunctorOver (pullback₂ {f = g} {p}) f) (k : MAP K T) (l : MAP L T) where
  k′ : MAP (Pullback k p) S
  k′ = pullback₂
  l′ : MAP (Pullback l p) S
  l′ = pullback₂
  g′ : MAP (Pullback g p) S
  g′ = pullback₂
  parameter = FunOver l g × FunOver k l
  module Old = Joint k l g using (functor)
  module New = Joint k′ l′ f using (functor; module At)
  module Inner = BaseChange p k l using (functor)
  module Outer = BaseChange p l g using (functor)
  module Whole = BaseChange p k g using (functor)
  module EvalK = Postcompose k′ ε using (functor)
  module EvalL = Postcompose l′ ε using (functor)
  module UK = Evaluation p f g ε k using (functor)
  module UL = Evaluation p f g ε l using (functor)
  module BC = Compositor p k l g using (source-evaluation; module Composite)
  module Composite = BC.Composite using (source; target; comparison; module Square; module Outer)
  inner-name : MAP parameter (FunOver k′ l′)
  inner-name = Inner.functor ∘ pr₂
  outer-name : MAP parameter (FunOver l′ f)
  outer-name = UL.functor ∘ pr₁
  module NewAt = New.At inner-name outer-name
    using (actual-inner; actual-outer; module ActualInner; evaluation)
  evaluated : MAP parameter (FunOver l′ f × FunOver k′ l′)
  evaluated = productMap UL.functor Inner.functor
  source : MAP parameter (FunOver k′ f)
  source = UK.functor ∘ Old.functor
  target : MAP parameter (FunOver k′ f)
  target = New.functor ∘ evaluated
  common = compose-over ε Composite.source

  opaque
    source-evaluation : FunctorOverIso (family k′ f source) common
    source-evaluation = compose-iso-over (postwhisker-over ε (inverse-iso-over Composite.comparison))
      (compose-iso-over (postwhisker-over ε BC.source-evaluation)
      (compose-iso-over (postcompose-family k′ ε (Whole.functor ∘ Old.functor))
        (family-identification k′ f (comp-assoc Old.functor Whole.functor EvalK.functor))))

    outer-evaluation : FunctorOverIso NewAt.actual-outer (compose-over ε Composite.Outer.pulled)
    outer-evaluation = compose-iso-over (postwhisker-over ε (Substitution.family-comparison p l g pr₁))
      (compose-iso-over (postcompose-family l′ ε (Outer.functor ∘ pr₁))
        (family-identification l′ f (comp-assoc pr₁ Outer.functor EvalL.functor)))

    target-evaluation : FunctorOverIso (family k′ f target) common
    target-evaluation = compose-iso-over
      (associator-over Composite.Square.V.over Composite.Outer.pulled ε)
      (compose-iso-over (prewhisker-over Composite.Square.V.over outer-evaluation)
      (compose-iso-over (postwhisker-over NewAt.actual-outer
        (Identification.comparison k′ l′ NewAt.actual-inner Composite.Square.B.pulled
          (Substitution.family-comparison p k l pr₂))) NewAt.evaluation))

    family-comparison : FunctorOverIso (family k′ f source) (family k′ f target)
    family-comparison = compose-iso-over (inverse-iso-over target-evaluation) source-evaluation

  module Lifted = CoherentLifting.Families 𝒯 M ℱ P k′ f source target
    using (action; lift; computation)

  opaque
    comparison : source =₁ target
    comparison = Lifted.lift family-comparison

    computation : FunctorOverIso₂ (Lifted.action comparison) family-comparison
    computation = Lifted.computation family-comparison

  restriction : {Y : CAT} (σ : MAP Y parameter) → (source ∘ σ) =₁ (target ∘ σ)
  restriction σ = comparison ▷ σ

  naturality : {Y : CAT} {σ τ : MAP Y parameter} (α : σ =₁ τ) →
    (restriction τ ∙ (source ◁ α)) =₂ ((target ◁ α) ∙ restriction σ)
  naturality α = interchange-at comparison α
```
