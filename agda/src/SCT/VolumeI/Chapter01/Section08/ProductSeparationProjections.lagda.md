# Projections of product separation

The separation comparison moves a parameter map past a functor in the
other coordinate. Both routes have specified comparisons with the same
product map. Taking their quotient, and then applying each projection,
retains those specified comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.ProductSeparationProjections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductComparisonProjections 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductCoordinateUnits 𝒯
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (inverse-composite)
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (coordinate-left-unit)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

quotient-projection : {R K C : CAT} (π : MAP K C)
  {s t w : MAP R K} {z : MAP R C}
  (b : NatIso (π ∘ w) z) (σ : NatIso s w) (τ : NatIso t w) →
  Iso₂ ((b ∙ (π ◁ τ)) ∙ (π ◁ (invIso τ ∙ σ))) (b ∙ (π ◁ σ))
quotient-projection π b σ τ = isoComp-cong (idIso b) (cancel-inverse (π ◁ τ) (π ◁ σ)) ∙
  (isoComp-assoc-at b (π ◁ τ) (invIso (π ◁ τ) ∙ (π ◁ σ)) ∙
    isoComp-cong (idIso (b ∙ (π ◁ τ)))
      (isoComp-cong (post-inverse π τ) (idIso (π ◁ σ)) ∙ postWhisker-isoComp-at π (invIso τ) σ))

module Separation {X Y A B : CAT} (h : MAP X Y) (f : MAP A B) where
  HA = productMap h (id A)
  HB = productMap h (id B)
  LX = productMap (id X) f
  LY = productMap (id Y) f
  module Source = Normalized h (id Y) (id A) f (comp-unitˡ h) (comp-unitʳ f)
  module Target = Normalized (id X) h f (id B) (comp-unitʳ h) (comp-unitˡ f)
  source = Source.value
  target = Target.value
  comparison = productMap-separate h f

  normalization : Iso₂ comparison (invIso target ∙ source)
  normalization = invIso
    (isoComp-assoc-at (invIso (productMap-comp (id X) h f (id B)))
      (invIso (productMap-cong (comp-unitʳ h) (comp-unitˡ f))) source ∙
      isoComp-cong (inverse-composite (productMap-cong (comp-unitʳ h) (comp-unitˡ f))
        (productMap-comp (id X) h f (id B))) (idIso source))

  sourceFirst = pair-β₁ (h ∘ pr₁) (id A ∘ pr₂) ∙ (comp-unitˡ pr₁ ▷ HA)
  sourceSecond = (f ◁ (comp-unitˡ pr₂ ∙ pair-β₂ (h ∘ pr₁) (id A ∘ pr₂))) ∙ comp-assoc HA pr₂ f
  targetFirst = (h ◁ (comp-unitˡ pr₁ ∙ pair-β₁ (id X ∘ pr₁) (f ∘ pr₂))) ∙ comp-assoc LX pr₁ h
  targetSecond = pair-β₂ (id X ∘ pr₁) (f ∘ pr₂) ∙ (comp-unitˡ pr₂ ▷ LX)
  sourceTail₁ = (pair-β₁ (id Y ∘ pr₁) (f ∘ pr₂) ▷ HA) ∙ invIso (comp-assoc HA LY pr₁)
  sourceTail₂ = (pair-β₂ (id Y ∘ pr₁) (f ∘ pr₂) ▷ HA) ∙ invIso (comp-assoc HA LY pr₂)
  targetTail₁ = (pair-β₁ (h ∘ pr₁) (id B ∘ pr₂) ▷ LX) ∙ invIso (comp-assoc LX HB pr₁)
  targetTail₂ = (pair-β₂ (h ∘ pr₁) (id B ∘ pr₂) ▷ LX) ∙ invIso (comp-assoc LX HB pr₂)
  sourceProjection₁ = sourceFirst ∙ sourceTail₁
  sourceProjection₂ = sourceSecond ∙ sourceTail₂
  targetProjection₁ = targetFirst ∙ targetTail₁
  targetProjection₂ = targetSecond ∙ targetTail₂

  source₁ : Iso₂ (pair-β₁ (h ∘ pr₁) (f ∘ pr₂) ∙ (pr₁ ◁ source)) sourceProjection₁
  source₁ = isoComp-cong
    (coordinate-left-unit pr₁ h pr₁ HA (pair-β₁ (h ∘ pr₁) (id A ∘ pr₂)))
    (idIso sourceTail₁) ∙ Source.projection₁

  source₂ : Iso₂ (pair-β₂ (h ∘ pr₁) (f ∘ pr₂) ∙ (pr₂ ◁ source)) sourceProjection₂
  source₂ = isoComp-cong
    (coordinate-inner-unit pr₂ pr₂ HA (pair-β₂ (h ∘ pr₁) (id A ∘ pr₂)) f)
    (idIso sourceTail₂) ∙ Source.projection₂

  target₁ : Iso₂ (pair-β₁ (h ∘ pr₁) (f ∘ pr₂) ∙ (pr₁ ◁ target)) targetProjection₁
  target₁ = isoComp-cong
    (coordinate-inner-unit pr₁ pr₁ LX (pair-β₁ (id X ∘ pr₁) (f ∘ pr₂)) h)
    (idIso targetTail₁) ∙ Target.projection₁

  target₂ : Iso₂ (pair-β₂ (h ∘ pr₁) (f ∘ pr₂) ∙ (pr₂ ◁ target)) targetProjection₂
  target₂ = isoComp-cong
    (coordinate-left-unit pr₂ f pr₂ LX (pair-β₂ (id X ∘ pr₁) (f ∘ pr₂)))
    (idIso targetTail₂) ∙ Target.projection₂

  abstract
    projection₁ : Iso₂ (targetProjection₁ ∙ (pr₁ ◁ comparison)) sourceProjection₁
    projection₁ = source₁ ∙
      (quotient-projection pr₁ (pair-β₁ (h ∘ pr₁) (f ∘ pr₂)) source target ∙
        isoComp-cong (invIso target₁) (postWhisker pr₁ ◁ normalization))

    projection₂ : Iso₂ (targetProjection₂ ∙ (pr₂ ◁ comparison)) sourceProjection₂
    projection₂ = source₂ ∙
      (quotient-projection pr₂ (pair-β₂ (h ∘ pr₁) (f ∘ pr₂)) source target ∙
        isoComp-cong (invIso target₂) (postWhisker pr₂ ◁ normalization))
```
