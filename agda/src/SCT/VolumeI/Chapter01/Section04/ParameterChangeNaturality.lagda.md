# Naturality of retained parameter change

The chosen comparison for changing a retained parameter factors through a
common pair of coordinates. We prove naturality of both factors and then
invert the second square. Thus this calculation refers to the comparison
already selected in `ParameterChange`, including its uncurrying witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section04.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section04.ParameterChangeNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open Compatibility 𝒯 M using (mapUncurry-restrict-inputs)
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
    → (pair (σ ∘ pr₁) (id D ∘ mapUncurry (f ∘ σ))) =₁ (common f)
  input-normalization f = pair-cong (idIso (σ ∘ pr₁))
    (mapUncurry-restrict f σ ∙ comp-unitˡ (mapUncurry (f ∘ σ)))

  output-normalization : (f : MAP P (Map C D))
    → (pair (pr₁ ∘ source-change) (mapUncurry f ∘ source-change)) =₁ (common f)
  output-normalization f = pair-cong (pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂))
    (idIso (mapUncurry f ∘ source-change))

  input-route : (f : MAP P (Map C D))
    → (target-change ∘ Retained.retained Q (f ∘ σ)) =₁ (common f)
  input-route f = input-normalization f ∙ productMap-pair σ (id D) pr₁ (mapUncurry (f ∘ σ))

  output-route : (f : MAP P (Map C D))
    → (Retained.retained P f ∘ source-change) =₁ (common f)
  output-route f = output-normalization f ∙ pair-pre pr₁ (mapUncurry f) source-change

  common-iso : {f g : MAP P (Map C D)} → f =₁ g → (common f) =₁ (common g)
  common-iso α = pair-cong (idIso (σ ∘ pr₁)) (mapUncurryIso α ▷ source-change)

  input-route-natural : {f g : MAP P (Map C D)} (α : f =₁ g)
    → (input-route g ∙ (target-change ◁ Retained.retainedIso Q (α ▷ σ))) =₂
        (common-iso α ∙ input-route f)
  input-route-natural {f} {g} α =
    let uα = mapUncurryIso α
        uασ = mapUncurryIso (α ▷ σ)
        left = idIso (σ ∘ pr₁)
        right = mapUncurry-restrict f σ ∙ comp-unitˡ (mapUncurry (f ∘ σ))
        right′ = mapUncurry-restrict g σ ∙ comp-unitˡ (mapUncurry (g ∘ σ))
        intermediate = pair-cong (σ ◁ idIso pr₁) (id D ◁ uασ)
        first-square = isoComp-cong (idIso left) (postWhisker-idIso σ pr₁)
        second-square = paste-squares
          (comp-unitˡ (mapUncurry (f ∘ σ))) (comp-unitˡ (mapUncurry (g ∘ σ)))
          (mapUncurry-restrict f σ) (mapUncurry-restrict g σ)
          (id D ◁ uασ) uασ (uα ▷ source-change)
          (postWhisker-id-at uασ) (mapUncurry-restrict-inputs α σ)
        normalize = pair-square left left right right′
          (σ ◁ idIso pr₁) left (id D ◁ uασ) (uα ▷ source-change)
          first-square second-square
    in paste-squares (productMap-pair σ (id D) pr₁ (mapUncurry (f ∘ σ)))
      (productMap-pair σ (id D) pr₁ (mapUncurry (g ∘ σ)))
      (input-normalization f) (input-normalization g)
      (target-change ◁ Retained.retainedIso Q (α ▷ σ)) intermediate (common-iso α)
      (productMap-pair-inner σ (id D) (idIso pr₁) uασ) normalize

  output-route-natural : {f g : MAP P (Map C D)} (α : f =₁ g)
    → (output-route g ∙ (Retained.retainedIso P α ▷ source-change)) =₂
        (common-iso α ∙ output-route f)
  output-route-natural {f} {g} α =
    let b = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
        uα = mapUncurryIso α ▷ source-change
        middle = pair-cong (idIso pr₁ ▷ source-change) uα
        first = (isoComp-unitˡ-at b) ⁻¹ ∙
          (isoComp-unitʳ-at b ∙ isoComp-cong (idIso b) (preWhisker-idIso pr₁ source-change))
        normalize = pair-square b b (idIso (mapUncurry f ∘ source-change))
          (idIso (mapUncurry g ∘ source-change))
          (idIso pr₁ ▷ source-change) (idIso (σ ∘ pr₁)) uα uα
          first (identity-square uα)
    in paste-squares (pair-pre pr₁ (mapUncurry f) source-change)
      (pair-pre pr₁ (mapUncurry g) source-change)
      (output-normalization f) (output-normalization g)
      (Retained.retainedIso P α ▷ source-change) middle (common-iso α)
      ((pair-pre-natural-inputs (idIso pr₁) (mapUncurryIso α) source-change) ⁻¹) normalize

retained-parameter-change-natural : {P Q C D : CAT}
  {f g : MAP P (Map C D)} (α : f =₁ g) (σ : MAP Q P)
  →
      (retained-parameter-change g σ ∙
        (productMap σ (id D) ◁ Retained.retainedIso Q (α ▷ σ))) =₂
      ((Retained.retainedIso P α ▷ productMap σ (id C)) ∙ retained-parameter-change f σ)
retained-parameter-change-natural {P} {Q} {C} {D} {f} {g} α σ =
  let open Routes σ
  in paste-squares (input-route f) (input-route g) ((output-route f) ⁻¹) ((output-route g) ⁻¹)
    (target-change ◁ Retained.retainedIso Q (α ▷ σ)) (common-iso α)
    (Retained.retainedIso P α ▷ source-change)
    (input-route-natural α)
    (move-square (output-route g) (Retained.retainedIso P α ▷ source-change)
      (common-iso α) (output-route f) (output-route-natural α))
```
