# Composition and endpoint evaluation

The comparison between successive postcomposition and postcomposition by
the composite is chosen with its uncurried image. Its evaluation equation
is retained. This supplies the coherence needed when pasting the
evaluation squares of Chapter 5.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.EvaluationComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β)
import SCT.VolumeI.Chapter02.Section01.EndpointNaturality as Natural
import SCT.VolumeI.Chapter02.Section02.PostcompositionParameterEvaluation as Parameter
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered; cancel-left)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module Composite {T A B C : CAT} (f : MAP A B) (g : MAP B C) where
  F = funPost {C = T} f
  G = funPost {C = T} g
  K = funPost {C = T} (g ∘ f)
  H = G ∘ F
  e = funEval {C = T} {D = A}
  b = funPost-β {C = T} f
  β₀ = funPost-β {C = T} (g ∘ f)
  a₀ = comp-assoc e f g
  β = a₀ ∙ β₀
  φ = funPost-uncurry g F
  θ = (g ◁ b) ∙ φ

  comparison : H =₁ K
  comparison = funIsoReflect H K (β ⁻¹ ∙ θ)

  module At (v : Obj-abs T) where
    i = insert {X = Fun T A} v
    Qh = evaluate-uncurry v H
    Qk = evaluate-uncurry v K
    Qf = evaluate-uncurry v F
    δ = evaluate v ◁ comparison
    assocBase = comp-assoc (evaluate v) f g
    af = comp-assoc i e f
    ak = comp-assoc i e (g ∘ f)
    a₁ = comp-assoc i (funUncurry F) g
    a₂ = comp-assoc i (f ∘ e) g
    n = evaluate-post-at v g F
    z = (b ▷ i) ∙ Qf
    w = (φ ▷ i) ∙ Qh
    raw = (θ ▷ i) ∙ Qh
    input = (β ▷ i) ∙ Qk
    result = evaluate-post v (g ∘ f) ∙ δ

    abstract
      reflected : (input ∙ δ) =₂ raw
      reflected = isoComp-cong
        ((preWhisker i ◁ (cancel-inverse β θ ∙
          isoComp-cong (idIso β) (funIsoReflect-β H K (β ⁻¹ ∙ θ)))) ∙
          (preWhisker-isoComp-at β (funUncurryIso comparison) i) ⁻¹)
        (idIso Qh) ∙
        (isoComp-assoc-at (β ▷ i) (funUncurryIso comparison ▷ i) Qh) ⁻¹ ∙
        isoComp-cong (idIso (β ▷ i)) (Natural.Evaluation.natural 𝒯 M ℱ v comparison) ∙
        isoComp-assoc-at (β ▷ i) Qk δ

    abstract
      raw-expand : raw =₂ (((g ◁ b) ▷ i) ∙ w)
      raw-expand = isoComp-assoc-at ((g ◁ b) ▷ i) (φ ▷ i) Qh ∙
        isoComp-cong (preWhisker-isoComp-at (g ◁ b) φ i) (idIso Qh)

    abstract
      raw-normal : (a₂ ∙ raw) =₂ ((g ◁ z) ∙ n)
      raw-normal = isoComp-cong ((postWhisker-isoComp-at g (b ▷ i) Qf) ⁻¹) (idIso n) ∙
        (isoComp-assoc-at (g ◁ (b ▷ i)) (g ◁ Qf) n) ⁻¹ ∙
        isoComp-cong (idIso (g ◁ (b ▷ i))) (Parameter.At.comparison 𝒯 M ℱ g F v) ∙
        isoComp-assoc-at (g ◁ (b ▷ i)) a₁ w ∙
        isoComp-cong (whisker-mixed-at b i g) (idIso w) ∙
        (isoComp-assoc-at a₂ ((g ◁ b) ▷ i) w) ⁻¹ ∙
        isoComp-cong (idIso a₂) raw-expand

    abstract
      input-expand : input =₂ ((a₀ ▷ i) ∙ ((β₀ ▷ i) ∙ Qk))
      input-expand = isoComp-assoc-at (a₀ ▷ i) (β₀ ▷ i) Qk ∙
        isoComp-cong (preWhisker-isoComp-at a₀ β₀ i) (idIso Qk)

    abstract
      left-normal : (assocBase ∙ result) =₂ ((g ◁ af) ∙ (a₂ ∙ raw))
      left-normal = isoComp-cong (idIso (g ◁ af))
          (isoComp-cong (idIso a₂) reflected ∙
            isoComp-cong (idIso a₂)
              (isoComp-cong (input-expand ⁻¹) (idIso δ))) ∙
        isoComp-assoc-at (g ◁ af) a₂ (((a₀ ▷ i) ∙ ((β₀ ▷ i) ∙ Qk)) ∙ δ) ∙
        isoComp-cong (idIso ((g ◁ af) ∙ a₂))
          ((isoComp-assoc-at (a₀ ▷ i) ((β₀ ▷ i) ∙ Qk) δ) ⁻¹) ∙
        isoComp-assoc-at ((g ◁ af) ∙ a₂) (a₀ ▷ i) (((β₀ ▷ i) ∙ Qk) ∙ δ) ∙
        isoComp-cong
          ((isoComp-assoc-at (g ◁ af) a₂ (a₀ ▷ i)) ⁻¹ ∙ pentagon-whiskered i e f g)
          (idIso (((β₀ ▷ i) ∙ Qk) ∙ δ)) ∙
        (isoComp-assoc-at assocBase ak (((β₀ ▷ i) ∙ Qk) ∙ δ)) ⁻¹ ∙
        isoComp-cong (idIso assocBase) (isoComp-assoc-at ak ((β₀ ▷ i) ∙ Qk) δ)

    abstract
      endpoint : (assocBase ∙ result) =₂ ((g ◁ evaluate-post v f) ∙ n)
      endpoint = isoComp-cong ((postWhisker-isoComp-at g af z) ⁻¹) (idIso n) ∙
        (isoComp-assoc-at (g ◁ af) (g ◁ z) n) ⁻¹ ∙
        isoComp-cong (idIso (g ◁ af)) raw-normal ∙ left-normal
```
