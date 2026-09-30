# The second coordinate of product substitution

The second coordinate of substitution by `σ × id C` is independent of
the functor in the first coordinate. Its composition law follows by
normalizing the identity functor's left unitor, using the already chosen
projection witness of the substitution comparison, and cancelling the
external associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FramedSubstitution as FramedSubstitution

module SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSecondCoordinate
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Compatibility 𝒯 M using (slice-comparison)
module Coordinates = ProductSubstitution.Coordinates 𝒯 M
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (coordinate-left-unit)
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (preWhisker-comp-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour; cancel-inverse)

private
  module Framed = FramedSubstitution vocabulary terminal products productLaws composition vertical whiskering
    using (module Composition)

second-normalization : {Y X Z : CAT} (C : CAT) (f : MAP X Z) (σ : MAP Y X)
  → (Coordinates.second C f σ) =₂
      (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂) ∙
        (comp-unitˡ pr₂ ▷ productMap σ (id C)))
second-normalization C f σ = coordinate-left-unit pr₂ (id C) pr₂ (productMap σ (id C))
  (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂))

second-coordinate-assoc : {W Y X Z : CAT} (C : CAT)
  (f : MAP X Z) (σ : MAP Y X) (τ : MAP W Y)
  →
      (Coordinates.second C f (σ ∘ τ) ∙
        (((id C ∘ pr₂) ◁ slice-comparison {C = C} σ τ) ∙
          comp-assoc (productMap τ (id C)) (productMap σ (id C)) (id C ∘ pr₂))) =₂
      ((idIso (id C) ▷ pr₂) ∙
        (Coordinates.second C (f ∘ σ) τ ∙
          (Coordinates.second C f σ ▷ productMap τ (id C))))
second-coordinate-assoc C f σ τ =
  let s = productMap σ (id C)
      t = productMap τ (id C)
      st = productMap (σ ∘ τ) (id C)
      κ = slice-comparison {C = C} σ τ
      q = id C ∘ pr₂
      b = pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
      bst = pair-β₂ ((σ ∘ τ) ∘ pr₁) (id C ∘ pr₂)
      S = Coordinates.second C f σ
      T = Coordinates.second C (f ∘ σ) τ
      normalized = T ∙ (S ▷ t)
      composition = Framed.Composition.compatible s t st κ q pr₂
        (id C ∘ pr₂) (id C ∘ pr₂) (comp-unitˡ pr₂) b bst S T
        (Coordinates.second C f (σ ∘ τ))
        (second-normalization C f σ)
        (second-normalization C f (σ ∘ τ))
        (Coordinates.projection₂ C σ τ)
      insertIdentity =
        (isoComp-unitˡ-at normalized ∙ isoComp-cong (preWhisker-idIso (id C) pr₂) (idIso normalized)) ⁻¹
  in insertIdentity ∙ composition
```
