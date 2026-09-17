# Product symmetry and restriction

We specify the comparison between restriction before and after product
symmetry by its two projections. These witnesses will also track the
matching of a transposed square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.SwapRestrictionData
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
module PS = Projections 𝒯

module Coordinates {X A B : CAT} (u : MAP A B) where
  input = swap {X} {A}
  output = swap {X} {B}
  source-step = productMap u (id X)
  target-step = productRestriction X u

  first-source-base : =₁ (pr₁ ∘ (source-step ∘ input)) (u ∘ pr₂)
  first-source-base = PS.compose-base pr₁ source-step
    (pair-β₁ (u ∘ pr₁) (id X ∘ pr₂)) input
    (PS.lift-base u pr₁ input (pair-β₁ pr₂ pr₁))

  first-target-base : =₁ (pr₁ ∘ (output ∘ target-step)) (u ∘ pr₂)
  first-target-base = PS.compose-base pr₁ output (pair-β₁ pr₂ pr₁)
    target-step (pair-β₂ (id X ∘ pr₁) (u ∘ pr₂))

  second-source-base : =₁ (pr₂ ∘ (source-step ∘ input)) pr₁
  second-source-base = PS.compose-base pr₂ source-step
    (comp-unitˡ pr₂ ∙ pair-β₂ (u ∘ pr₁) (id X ∘ pr₂)) input (pair-β₂ pr₂ pr₁)

  second-target-base : =₁ (pr₂ ∘ (output ∘ target-step)) pr₁
  second-target-base = PS.compose-base pr₂ output (pair-β₂ pr₂ pr₁)
    target-step (comp-unitˡ pr₁ ∙ pair-β₁ (id X ∘ pr₁) (u ∘ pr₂))

  first = invIso first-target-base ∙ first-source-base
  second = invIso second-target-base ∙ second-source-base

  value : =₁ (source-step ∘ input) (output ∘ target-step)
  value = pair-iso first second

  abstract
    projection₁ : PS.Square pr₁ first-source-base first-target-base value
    projection₁ = cancel-inverse first-target-base first-source-base ∙
      isoComp-cong (idIso first-target-base) (pair-iso-β₁ first second)

    projection₂ : PS.Square pr₂ second-source-base second-target-base value
    projection₂ = cancel-inverse second-target-base second-source-base ∙
      isoComp-cong (idIso second-target-base) (pair-iso-β₂ first second)

swap-restriction : {X A B : CAT} (u : MAP A B) →
  =₁ (productMap u (id X) ∘ swap {X} {A})
    (swap {X} {B} ∘ productRestriction X u)
swap-restriction = Coordinates.value
```
