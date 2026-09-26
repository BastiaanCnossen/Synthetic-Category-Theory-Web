# The base-changed family over the original base

Base change initially gives a functor over `C`. Postcompose that base
with `C → S` and use the two specified pullback matchings to regard the
family over `S`. This family is defined before composing with evaluation;
its triangle depends only on the base-change data.

The last comparison cancels the intermediate pullback matching. It
identifies literal postcomposition by the internal evaluation triangle
with the projected dependent-product family.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.InternalProductFamily
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target; forward-composite)
open import SCT.VolumeI.Chapter03.Section05.Currying.PullbackTargetFamilies 𝒯 M ℱ P using (module Families)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (module Curry)
import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families as FamilyCalculus
module FC = FamilyCalculus 𝒯 M ℱ P

module Product {C D S E R : CAT} (p : MAP C S) (q : MAP D S) (g : MAP R S)
  (ε : FunctorOver (pullback₂ {f = g} {p}) (pullback₂ {f = q} {p})) (t : MAP E S) where
  module BC = BaseChange p t g
  structure : MAP (Pullback g p) S
  structure = g ∘ pullback₁
  source-structure : MAP (Pullback t p) S
  source-structure = t ∘ pullback₁
  evaluation-triangle : FunctorOver structure q
  evaluation-triangle = change-source (pullbackMatch {f = g} {p} ⁻¹) (Target.forward p q BC.g′ ε)
  α = pullbackMatch {f = t} {p} ⁻¹ ▷ pr₂ {C = FunOver t g}
  γ = pullbackMatch {f = g} {p}
  assoc = comp-assoc (pr₂ {C = FunOver t g}) BC.f′ p
  δ = α ∙ assoc ⁻¹

  family : FunctorOver (source-structure ∘ pr₂ {C = FunOver t g}) structure
  family = change-source δ (change-target-back γ (postbase p BC.evaluated))

  evaluated : FunctorOver (source-structure ∘ pr₂ {C = FunOver t g}) q
  evaluated = compose-over evaluation-triangle family

  projected : FunctorOver (source-structure ∘ pr₂ {C = FunOver t g}) q
  projected = change-source α (Families.forward p q BC.f′ (compose-over ε BC.evaluated))

  base-family : FunctorOver (p ∘ (BC.f′ ∘ pr₂ {C = FunOver t g})) (p ∘ BC.g′)
  base-family = postbase p BC.evaluated

  projected-evaluation : FunctorOver (p ∘ BC.g′) q
  projected-evaluation = Target.forward p q BC.g′ ε

  cancelled : FunctorOver (source-structure ∘ pr₂ {C = FunOver t g}) q
  cancelled = change-source δ (compose-over projected-evaluation base-family)

  separated : FunctorOver (source-structure ∘ pr₂ {C = FunOver t g}) q
  separated = change-source α (change-source (assoc ⁻¹) (compose-over projected-evaluation base-family))

  abstract
    move-source : FunctorOverIso evaluated
      (change-source δ (compose-over evaluation-triangle (change-target-back γ base-family)))
    move-source = compose-source-change δ (change-target-back γ base-family) evaluation-triangle

    cancel-matching : FunctorOverIso
      (compose-over evaluation-triangle (change-target-back γ base-family))
      (compose-over projected-evaluation base-family)
    cancel-matching = Cancellation.comparison γ base-family projected-evaluation

    separate-source : FunctorOverIso cancelled separated
    separate-source = inverse-iso-over (source-change-composite α (assoc ⁻¹)
      (compose-over projected-evaluation base-family))

    project-composite : FunctorOverIso separated projected
    project-composite = change-source-iso α (change-source-iso (assoc ⁻¹)
      (inverse-iso-over (forward-composite p q ε BC.evaluated)))

    comparison : FunctorOverIso evaluated projected
    comparison = compose-iso-over project-composite
      (compose-iso-over separate-source
        (compose-iso-over (change-source-iso δ cancel-matching) move-source))

  functor : MAP (FunOver t g) (FunOver (source-structure) structure)
  functor = Curry.functor (source-structure) structure
    (FunctorLift.lift family) (FunctorLift.comparison family)

  maps : MAP (MapOver t g) (MapOver (source-structure) structure)
  maps = mapPost functor

  abstract
    family-comparison : FunctorOverIso
      (FC.family (source-structure) structure functor) family
    family-comparison = FC.curried-beta (source-structure) structure family
```
