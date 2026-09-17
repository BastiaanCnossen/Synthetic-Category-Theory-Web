# Naturality of retained parameter change

The chosen comparison for changing a retained parameter factors through a
common pair of coordinates. We prove naturality of both factors and then
invert the second square. Thus this calculation refers to the comparison
already selected in `ParameterChange`, including its uncurrying witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section03.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section03.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section03.ParameterChangeNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open Compatibility 𝒯 M using (mapUncurry-pre-inputs)
open MapComposition 𝒯 M using (productMap-pair)
open ParameterChange 𝒯 M using (retained-parameter-change)
module Retained = InternalCoherence.RetainedEvaluation 𝒯 M
open CompositionNaturality 𝒯 M using (productMap-pair-inner; identity-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-id-at)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-inputs; move-square)

module Routes {P Q C D : CAT} (σ : MAP Q P) where

  source-change : MAP (Q × C) (P × C)
  source-change = productMap σ (id C)

  target-change : MAP (Q × D) (P × D)
  target-change = productMap σ (id D)

  common : MAP P (Map C D) → MAP (Q × C) (P × D)
  common f = pair (σ ∘ pr₁) (mapUncurry f ∘ source-change)

  input-normalization : (f : MAP P (Map C D))
    → NatIso (pair (σ ∘ pr₁) (id D ∘ mapUncurry (f ∘ σ))) (common f)
  input-normalization f = pair-cong (idIso (σ ∘ pr₁))
    (mapUncurry-pre f σ ∙ comp-unitˡ (mapUncurry (f ∘ σ)))

  output-normalization : (f : MAP P (Map C D))
    → NatIso (pair (pr₁ ∘ source-change) (mapUncurry f ∘ source-change)) (common f)
  output-normalization f = pair-cong (pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂))
    (idIso (mapUncurry f ∘ source-change))

  input-route : (f : MAP P (Map C D))
    → NatIso (target-change ∘ Retained.retained Q (f ∘ σ)) (common f)
  input-route f = input-normalization f ∙ productMap-pair σ (id D) pr₁ (mapUncurry (f ∘ σ))

  output-route : (f : MAP P (Map C D))
    → NatIso (Retained.retained P f ∘ source-change) (common f)
  output-route f = output-normalization f ∙ pair-pre pr₁ (mapUncurry f) source-change

  common-iso : {f g : MAP P (Map C D)} → NatIso f g → NatIso (common f) (common g)
  common-iso α = pair-cong (idIso (σ ∘ pr₁)) (mapUncurryIso α ▷ source-change)

  input-route-natural : {f g : MAP P (Map C D)} (α : NatIso f g)
    → Iso₂ (input-route g ∙ (target-change ◁ Retained.retainedIso Q (α ▷ σ)))
        (common-iso α ∙ input-route f)
  input-route-natural {f} {g} α =
    let uα = mapUncurryIso α
        uασ = mapUncurryIso (α ▷ σ)
        left = idIso (σ ∘ pr₁)
        right = mapUncurry-pre f σ ∙ comp-unitˡ (mapUncurry (f ∘ σ))
        right′ = mapUncurry-pre g σ ∙ comp-unitˡ (mapUncurry (g ∘ σ))
        intermediate = pair-cong (σ ◁ idIso pr₁) (id D ◁ uασ)
        first-square = isoComp-cong (idIso left) (postWhisker-idIso σ pr₁)
        second-square = paste-squares
          (comp-unitˡ (mapUncurry (f ∘ σ))) (comp-unitˡ (mapUncurry (g ∘ σ)))
          (mapUncurry-pre f σ) (mapUncurry-pre g σ)
          (id D ◁ uασ) uασ (uα ▷ source-change)
          (postWhisker-id-at uασ) (mapUncurry-pre-inputs α σ)
        normalize = pair-square left left right right′
          (σ ◁ idIso pr₁) left (id D ◁ uασ) (uα ▷ source-change)
          first-square second-square
    in paste-squares (productMap-pair σ (id D) pr₁ (mapUncurry (f ∘ σ)))
      (productMap-pair σ (id D) pr₁ (mapUncurry (g ∘ σ)))
      (input-normalization f) (input-normalization g)
      (target-change ◁ Retained.retainedIso Q (α ▷ σ)) intermediate (common-iso α)
      (productMap-pair-inner σ (id D) (idIso pr₁) uασ) normalize

  output-route-natural : {f g : MAP P (Map C D)} (α : NatIso f g)
    → Iso₂ (output-route g ∙ (Retained.retainedIso P α ▷ source-change))
        (common-iso α ∙ output-route f)
  output-route-natural {f} {g} α =
    let b = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
        uα = mapUncurryIso α ▷ source-change
        middle = pair-cong (idIso pr₁ ▷ source-change) uα
        first = invIso (isoComp-unitˡ-at b) ∙
          (isoComp-unitʳ-at b ∙ isoComp-cong (idIso b) (preWhisker-idIso pr₁ source-change))
        normalize = pair-square b b (idIso (mapUncurry f ∘ source-change))
          (idIso (mapUncurry g ∘ source-change))
          (idIso pr₁ ▷ source-change) (idIso (σ ∘ pr₁)) uα uα
          first (identity-square uα)
    in paste-squares (pair-pre pr₁ (mapUncurry f) source-change)
      (pair-pre pr₁ (mapUncurry g) source-change)
      (output-normalization f) (output-normalization g)
      (Retained.retainedIso P α ▷ source-change) middle (common-iso α)
      (invIso (pair-pre-natural-inputs (idIso pr₁) (mapUncurryIso α) source-change)) normalize

retained-parameter-change-natural : {P Q C D : CAT}
  {f g : MAP P (Map C D)} (α : NatIso f g) (σ : MAP Q P)
  → Iso₂
      (retained-parameter-change g σ ∙
        (productMap σ (id D) ◁ Retained.retainedIso Q (α ▷ σ)))
      ((Retained.retainedIso P α ▷ productMap σ (id C)) ∙ retained-parameter-change f σ)
retained-parameter-change-natural {P} {Q} {C} {D} {f} {g} α σ =
  let open Routes σ
  in paste-squares (input-route f) (input-route g) (invIso (output-route f)) (invIso (output-route g))
    (target-change ◁ Retained.retainedIso Q (α ▷ σ)) (common-iso α)
    (Retained.retainedIso P α ▷ source-change)
    (input-route-natural α)
    (move-square (output-route g) (Retained.retainedIso P α ▷ source-change)
      (common-iso α) (output-route f) (output-route-natural α))
```
