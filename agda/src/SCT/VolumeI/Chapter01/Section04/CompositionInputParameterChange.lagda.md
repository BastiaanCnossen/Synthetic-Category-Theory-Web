# Comparing the two composition restriction routes

The independent input calculation and the output calculation use
definitionally identical route expressions. Their common application
normalization cancels to give the required composition square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.CompositionInputCalculus as Input
import SCT.VolumeI.Chapter01.Section04.CompositionParameterChange as Output
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section04.CompositionInputParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
module Boundaries = Output.UncurriedCompositionRestriction 𝒯 M
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect)

abstract
  composition-input-normalization : {P Q C D E : CAT}
    (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P)
    → (Boundaries.target-normalization g f σ ∙ Boundaries.change-input g f σ) =₂
        (Boundaries.application-route g f σ)
  composition-input-normalization = Input.composition-input-normalization 𝒯 M

  uncurry-compose-parameter-change : {P Q C D E : CAT}
    (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P)
    → (Boundaries.change-input g f σ) =₂ (Boundaries.restrict-output g f σ)
  uncurry-compose-parameter-change g f σ =
    cancel-left-reflect (Boundaries.target-normalization g f σ)
      ((Boundaries.restrict-output-normalization g f σ) ⁻¹ ∙
        composition-input-normalization g f σ)
```