# The interval boundary induces an equivalence on cores

The interval-core axiom identifies the specified endpoint copairing
with the core inclusion. The same remains true after taking its product
with an arbitrary category. This prepares the core calculation for joins.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter02.Section01.IntervalCore as IntervalCore

module SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.BoundaryCore
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (K : IntervalCore.IntervalCoreAxiom 𝒯 M B I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (productMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section04.MappingProducts 𝒯 M
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan 𝒯 M B P U I using (boundary)
open import SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinBoundary 𝒯 M B P U I using (weakened-boundary)
open IntervalCore 𝒯 M B I using (intervalCore)
open IntervalCore.IntervalCoreAxiom K

abstract
  boundary-comparison : (coreInclusion [1] ∘ intervalCore) =₁ boundary
  boundary-comparison = copair-cong (coreInclusion-name zero) (coreInclusion-name one) ∙
    copair-post (nameMap zero) (nameMap one) (coreInclusion [1])

  boundary-core-isEquiv : IsEquiv (mapPost {C = One} boundary)
  boundary-core-isEquiv = equiv-transport
    (mapPost-cong boundary-comparison ∙ mapPost-comp intervalCore (coreInclusion [1]))
    (equiv-compose (mapPost intervalCore) (mapPost (coreInclusion [1]))
      (mapPost-isEquiv intervalCore intervalCore-isEquiv) (core-universal One [1] one-isAn))

module ProductCore {C C′ D D′ : CAT} (f : MAP C C′) (g : MAP D D′) where
  module Source = ProductComparison One C D
  module Target = ProductComparison One C′ D′
  F : MAP (Core C) (Core C′)
  F = mapPost f
  G : MAP (Core D) (Core D′)
  G = mapPost g
  combined : MAP (Core (C × D)) (Core (C′ × D′))
  combined = mapPost (productMap f g)

  abstract
    natural : (Target.forward ∘ combined) =₁ (productMap F G ∘ Source.forward)
    natural = pair-iso (right-first ⁻¹ ∙ left-first) (right-second ⁻¹ ∙ left-second)
      where
      left-first : (pr₁ ∘ (Target.forward ∘ combined)) =₁ mapPost (f ∘ pr₁)
      left-first = mapPost-cong (pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) ∙
        (mapPost-comp (productMap f g) pr₁ ∙ project-pair₁ (mapPost pr₁) (mapPost pr₂) combined)
      left-second : (pr₂ ∘ (Target.forward ∘ combined)) =₁ mapPost (g ∘ pr₂)
      left-second = mapPost-cong (pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) ∙
        (mapPost-comp (productMap f g) pr₂ ∙ project-pair₂ (mapPost pr₁) (mapPost pr₂) combined)
      right-first : (pr₁ ∘ (productMap F G ∘ Source.forward)) =₁ mapPost (f ∘ pr₁)
      right-first = mapPost-comp pr₁ f ∙
        ((F ◁ pair-β₁ (mapPost pr₁) (mapPost pr₂)) ∙
          (comp-assoc Source.forward pr₁ F ∙ project-pair₁ (F ∘ pr₁) (G ∘ pr₂) Source.forward))
      right-second : (pr₂ ∘ (productMap F G ∘ Source.forward)) =₁ mapPost (g ∘ pr₂)
      right-second = mapPost-comp pr₂ g ∙
        ((G ◁ pair-β₂ (mapPost pr₁) (mapPost pr₂)) ∙
          (comp-assoc Source.forward pr₂ G ∙ project-pair₂ (F ∘ pr₁) (G ∘ pr₂) Source.forward))

    isEquiv : IsEquiv F → IsEquiv G → IsEquiv combined
    isEquiv ef eg = equiv-cancel-left combined Target.forward Target.forward-isEquiv
      (equiv-transport (natural ⁻¹)
        (equiv-compose Source.forward (productMap F G) Source.forward-isEquiv (productMap-isEquiv F G ef eg)))

weakened-boundary-core-isEquiv : (Γ : CAT) → IsEquiv (mapPost {C = One} (weakened-boundary Γ))
weakened-boundary-core-isEquiv Γ = ProductCore.isEquiv (id Γ) boundary
  (mapPost-isEquiv (id Γ) (id-isEquiv Γ)) boundary-core-isEquiv
```
