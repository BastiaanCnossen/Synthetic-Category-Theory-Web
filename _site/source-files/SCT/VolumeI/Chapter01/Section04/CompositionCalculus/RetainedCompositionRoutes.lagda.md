# Routes for retained composition and parameter change

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting as ParameterSquarePasting

module SCT.VolumeI.Chapter01.Section04.CompositionCalculus.RetainedCompositionRoutes
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M
open InternalCoherence 𝒯 M
open ParameterChange 𝒯 M using (retained-parameter-change)
open ParameterSquarePasting 𝒯 using (paste)
```
The two retained routes use the composition comparison already selected
in `InternalCoherence`. The restriction comparison for composition occurs
on the input side, so its retained image is inverted in the second route.

```agda
module Routes {P Q C D E : CAT}
  (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P) where
  module RP = RetainedEvaluation P
  module RQ = RetainedEvaluation Q

  σC = productMap σ (id C)
  σD = productMap σ (id D)
  σE = productMap σ (id E)

  κf = retained-parameter-change f σ
  κg = retained-parameter-change g σ
  κcomp = retained-parameter-change (composeTerm g f) σ
  δ = composeTerm-pre g f σ

  source : MAP (Q × C) (P × E)
  source = σE ∘ RQ.retained (composeTerm (g ∘ σ) (f ∘ σ))

  target : MAP (Q × C) (P × E)
  target = (RP.retained g ∘ RP.retained f) ∘ σC

  change-input : source =₁ target
  change-input = paste κg κf ∙ (σE ◁ RQ.retained-compose (g ∘ σ) (f ∘ σ))

  restrict-output : source =₁ target
  restrict-output = (RP.retained-compose g f ▷ σC) ∙
    (κcomp ∙ (σE ◁ RQ.retainedIso δ) ⁻¹)
```
