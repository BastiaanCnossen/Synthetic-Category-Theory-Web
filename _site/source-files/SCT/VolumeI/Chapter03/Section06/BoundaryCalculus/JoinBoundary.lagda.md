# The height of the join boundary

The two summands lie over the zero and one sections of the interval.
The comparison below relates their map into `Γ × ∂[1]` to the height
cocone. It will specify the canonical boundary pullback comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval

module SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinBoundary
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan 𝒯 M B P U I

weakened-boundary : (Γ : CAT) → MAP (Γ × ∂[1]) (Γ × [1])
weakened-boundary Γ = productMap (id Γ) boundary

module Boundary {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) where
  module Diagram = Span p q

  projection : MAP (C ⊔ D) (Γ × ∂[1])
  projection = copair (pair p (const in₁)) (pair q (const in₂))

  component : {A : CAT} (v : MAP A Γ) (i : MAP One ∂[1])
    (e : Obj-abs [1]) (β : (boundary ∘ i) =₁ e) →
    (weakened-boundary Γ ∘ pair v (const i)) =₁ pair v (const e)
  component {A} v i e β = pair-cong
    (comp-unitˡ v ∙ ((id Γ ◁ pair-β₁ v (const i)) ∙
      comp-assoc (pair v (const i)) pr₁ (id Γ)))
    ((β ▷ terminate A) ∙ ((comp-assoc (terminate A) i boundary) ⁻¹ ∙
      ((boundary ◁ pair-β₂ v (const i)) ∙
        comp-assoc (pair v (const i)) pr₂ boundary))) ∙
    pair-pre (id Γ ∘ pr₁) (boundary ∘ pr₂) (pair v (const i))

  abstract
    comparison : (weakened-boundary Γ ∘ projection) =₁ Diagram.boundary-height
    comparison = copair-cong
      (component p in₁ zero (copair-β₁ zero one))
      (component q in₂ one (copair-β₂ zero one)) ∙
      copair-post (pair p (const in₁)) (pair q (const in₂)) (weakened-boundary Γ)
```
