# The normalized outer precomposition frame

The evaluated whiskering of the chosen unit has the same outer frame as
the precomposition functor followed by its right unitor. Product eta,
identity evaluation, and both constant-coordinate unitors are retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionOuterFrame
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite; inverse-inverse)
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedProjectionNormalization as Projection
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionUnitEvaluation as Unit
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-Iso₂)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {C D : CAT} (K : CAT) (r : MAP D C) where
  module Evaluated = Unit.At 𝒯 M ℱ K r
  X = Evaluated.X
  L = Evaluated.L
  e = Evaluated.e
  W = Evaluated.W
  tC = funUncurry-id C K
  T₀ = comp-unitʳ e ∙ (e ◁ pair-projections)
  unit-source = (tC ⁻¹ ∙ T₀) ⁻¹
  first = comp-unitˡ pr₁ ∙ pair-β₁ (id X ∘ pr₁) (r ∘ pr₂)
  second = pair-β₂ (id X ∘ pr₁) (r ∘ pr₂)
  product-frame = pair-cong first second ∙ pair-pre pr₁ pr₂ W
  source-frame = (e ◁ product-frame) ∙ comp-assoc W (pair pr₁ pr₂) e
  δ = pair-cong (comp-unitˡ (pr₁ {X} {D})) (idIso (r ∘ pr₂ {X} {D}))
  outside = (e ◁ δ) ∙ Evaluated.β
  module ProjectionFrame = Projection.At 𝒯 M e (comp-unitˡ (pr₁ {X} {D})) (idIso (r ∘ pr₂ {X} {D}))

  abstract
    product-normal : product-frame =₂ ProjectionFrame.product-frame
    product-normal = isoComp-cong (pair-cong-Iso₂ (idIso first) ((isoComp-unitˡ-at second) ⁻¹))
      (idIso (pair-pre pr₁ pr₂ W))

    frame-normal : source-frame =₂ ((e ◁ δ) ∙ (T₀ ▷ W))
    frame-normal = ProjectionFrame.value ∙
      isoComp-cong (postWhisker e ◁ product-normal) (idIso (comp-assoc W (pair pr₁ pr₂) e))

    identity-cancel : (T₀ ∙ unit-source) =₂ tC
    identity-cancel = inverse-inverse tC ∙ cancel-inverse T₀ (tC ⁻¹ ⁻¹) ∙
      isoComp-cong (idIso T₀) (inverse-composite (tC ⁻¹) T₀)

    prefix : (source-frame ∙ (unit-source ▷ W)) =₂ ((e ◁ δ) ∙ (tC ▷ W))
    prefix = isoComp-cong (idIso (e ◁ δ)) (preWhisker W ◁ identity-cancel) ∙
      isoComp-cong (idIso (e ◁ δ)) ((preWhisker-isoComp-at T₀ unit-source W) ⁻¹) ∙
      isoComp-assoc-at (e ◁ δ) (T₀ ▷ W) (unit-source ▷ W) ∙
      isoComp-cong frame-normal (idIso (unit-source ▷ W))

    value : (source-frame ∙ ((unit-source ▷ W) ∙ funPre-uncurry r (id X))) =₂
      (outside ∙ funUncurryIso (comp-unitʳ L))
    value = (isoComp-assoc-at (e ◁ δ) Evaluated.β (funUncurryIso (comp-unitʳ L))) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ δ)) Evaluated.value ∙
      isoComp-assoc-at (e ◁ δ) (tC ▷ W) (funPre-uncurry r (id X)) ∙
      isoComp-cong prefix (idIso (funPre-uncurry r (id X))) ∙
      (isoComp-assoc-at source-frame (unit-source ▷ W) (funPre-uncurry r (id X))) ⁻¹
```
