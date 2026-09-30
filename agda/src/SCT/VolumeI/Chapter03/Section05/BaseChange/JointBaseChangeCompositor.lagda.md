# The joint base-change compositor

Base change commutes with joint composition of relative functors.
Prove the comparison on the product of the two relative functor
categories: evaluate both sides, use the base-change comparison for
composite families, and lift the resulting native identification.
The lifting computation retains its triangle over the base.

The compositor is chosen once on this common parameter. Its restrictions
are natural by interchange. This does not identify those restrictions
with the earlier pointwise native compositor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.RelativeCategories.Families.CoherentRelativeFamilyLifting as CoherentLifting
import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeFamilyProjection as FamilyIdentifications

module SCT.VolumeI.Chapter03.Section05.BaseChange.JointBaseChangeCompositor
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family; curried-beta)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeSubstitution 𝒯 M ℱ P using (module Substitution)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.JointComposition 𝒯 M ℱ P using (module Joint)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.RetainedRelativeFamilies 𝒯 M ℱ P using (module Identification)
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeRetainedFamilies 𝒯 M ℱ P using (module CompositeFamilies)

module Compositor {A B C S T : CAT} (p : MAP S T)
  (f : MAP A T) (g : MAP B T) (h : MAP C T) where
  f′ : MAP (Pullback f p) S
  f′ = pullback₂
  g′ : MAP (Pullback g p) S
  g′ = pullback₂
  h′ : MAP (Pullback h p) S
  h′ = pullback₂
  parameter = FunOver g h × FunOver f g
  module Old = Joint f g h using (functor; inner; outer; composite)
  module New = Joint f′ g′ h′ using (functor; module At)
  module Bfg = BaseChange p f g using (functor)
  module Bgh = BaseChange p g h using (functor)
  module Bfh = BaseChange p f h using (functor)
  module Composite = CompositeFamilies p f g h Old.inner Old.outer
    using (source; target; comparison; module Square; module Outer)
  inner-name : MAP parameter (FunOver f′ g′)
  inner-name = Bfg.functor ∘ pr₂
  outer-name : MAP parameter (FunOver g′ h′)
  outer-name = Bgh.functor ∘ pr₁
  module NewAt = New.At inner-name outer-name using (actual-inner; actual-outer; module ActualInner; evaluation)

  source : MAP parameter (FunOver f′ h′)
  source = Bfh.functor ∘ Old.functor
  target : MAP parameter (FunOver f′ h′)
  target = New.functor ∘ productMap Bgh.functor Bfg.functor

  opaque
    source-evaluation : FunctorOverIso (family f′ h′ source) Composite.target
    source-evaluation = compose-iso-over
      (FamilyIdentifications.Identification.comparison 𝒯 M ℱ P p f h (curried-beta f h Old.composite))
      (Substitution.family-comparison p f h Old.functor)

    target-evaluation : FunctorOverIso (family f′ h′ target) Composite.source
    target-evaluation = compose-iso-over
      (postwhisker-over Composite.Outer.pulled
        (Identification.comparison f′ g′ NewAt.actual-inner Composite.Square.B.pulled
          (Substitution.family-comparison p f g pr₂)))
      (compose-iso-over
        (prewhisker-over NewAt.ActualInner.over (Substitution.family-comparison p g h pr₁))
        NewAt.evaluation)

    family-comparison : FunctorOverIso (family f′ h′ source) (family f′ h′ target)
    family-comparison = compose-iso-over (inverse-iso-over target-evaluation)
      (compose-iso-over (inverse-iso-over Composite.comparison) source-evaluation)

  module Lifted = CoherentLifting.Families 𝒯 M ℱ P f′ h′ source target
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
