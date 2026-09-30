# Composite and identity endpoints of separation

The normalized separation comparison applies to a nested composite and
to the identity endpoint. The latter also retains the chosen comparisons
from the pair of projections to the identity functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.SeparationEndpointTransport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.SeparationFrameTransport as Transport
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.NestedCoordinateNaturality as Nested
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductPairingComparisons 𝒯 M using (identity-coordinate)
open import SCT.VolumeI.Chapter01.Section04.Substitution.RetainedIdentityParameterChange 𝒯 M using (pair-projections-pre; pair-projections-post)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-comp; pair-cong-Iso₂)
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)

module Composite {X Y A B C : CAT} (h : MAP X Y) (f : MAP A B) (g : MAP B C) where
  σ = productMap h (id A)
  ρ₂ = comp-unitˡ pr₂ ∙ pair-β₂ (h ∘ pr₁) (id A ∘ pr₂)
  module Coordinate = Nested.At 𝒯 σ pr₂ ρ₂ f g
  module Changed = Transport.At 𝒯 M h (g ∘ f)
    (comp-assoc (pr₂ {Y} {A}) f g) (comp-assoc (pr₂ {X} {A}) f g) Coordinate.distributed
  abstract
    value : (Changed.F.target-frame ∙ Changed.ν) =₂ Changed.F.source-frame
    value = Changed.value Coordinate.square

module Identity {X Y A : CAT} (h : MAP X Y) where
  σ = productMap h (id A)
  ρ₂ = comp-unitˡ pr₂ ∙ pair-β₂ (h ∘ pr₁) (id A ∘ pr₂)
  module Changed = Transport.At 𝒯 M h (id A)
    (comp-unitˡ (pr₂ {Y} {A})) (comp-unitˡ (pr₂ {X} {A})) ρ₂
  c₀ : σ =₁ pair (h ∘ pr₁ {X} {A}) (pr₂ {X} {A})
  c₀ = pair-cong (idIso (h ∘ pr₁)) (comp-unitˡ pr₂)
  left = comp-unitˡ σ ∙ (pair-projections ▷ σ)
  right = comp-unitʳ σ ∙ (σ ◁ pair-projections)

  abstract
    coordinate : (ρ₂ ∙ (comp-unitˡ pr₂ ▷ σ)) =₂
      (comp-unitˡ pr₂ ∙ Changed.F.N.source-second)
    coordinate = (identity-coordinate pr₂ σ ρ₂) ⁻¹

    value : (Changed.F.target-frame ∙ Changed.ν) =₂ Changed.F.source-frame
    value = Changed.value coordinate

    source-normal : (c₀ ∙ left) =₂ Changed.F.source-frame
    source-normal = isoComp-cong (pair-cong-Iso₂ (isoComp-unitˡ-at Changed.F.N.ρ₁) (idIso ρ₂))
        (idIso (pair-pre pr₁ pr₂ σ)) ∙
      isoComp-cong ((pair-cong-comp (idIso (h ∘ pr₁)) Changed.F.N.ρ₁
          (comp-unitˡ pr₂) (pair-β₂ (h ∘ pr₁) (id A ∘ pr₂))) ⁻¹)
        (idIso (pair-pre pr₁ pr₂ σ)) ∙
      (isoComp-assoc-at c₀ (pair-cong Changed.F.N.ρ₁ (pair-β₂ (h ∘ pr₁) (id A ∘ pr₂)))
        (pair-pre pr₁ pr₂ σ)) ⁻¹ ∙
      isoComp-cong (idIso c₀) (pair-projections-pre (h ∘ pr₁) (id A ∘ pr₂))

    target-normal : (c₀ ∙ right) =₂ Changed.F.target-frame
    target-normal = isoComp-cong (idIso c₀) (pair-projections-post h (id A))

    unit-square : (right ∙ Changed.ν) =₂ left
    unit-square = cancel-left-reflect c₀
      (source-normal ⁻¹ ∙ value ∙
        isoComp-cong target-normal (idIso Changed.ν) ∙
        (isoComp-assoc-at c₀ right Changed.ν) ⁻¹)
```
