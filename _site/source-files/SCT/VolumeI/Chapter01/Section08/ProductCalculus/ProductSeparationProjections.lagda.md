# Projections of product separation

The separation comparison moves a parameter map past a functor in the
other coordinate. Both routes have specified comparisons with the same
product map. Taking their quotient, and then applying each projection,
retains those specified comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSeparationProjections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductComparisonProjections 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductCoordinateUnits 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (coordinate-left-unit)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

quotient-projection : {R K C : CAT} (π : MAP K C)
  {s t w : MAP R K} {z : MAP R C}
  (b : (π ∘ w) =₁ z) (σ : s =₁ w) (τ : t =₁ w) →
  ((b ∙ (π ◁ τ)) ∙ (π ◁ (τ ⁻¹ ∙ σ))) =₂ (b ∙ (π ◁ σ))
quotient-projection π b σ τ = isoComp-cong (idIso b) (cancel-inverse (π ◁ τ) (π ◁ σ)) ∙
  (isoComp-assoc-at b (π ◁ τ) ((π ◁ τ) ⁻¹ ∙ (π ◁ σ)) ∙
    isoComp-cong (idIso (b ∙ (π ◁ τ)))
      (isoComp-cong (post-inverse π τ) (idIso (π ◁ σ)) ∙ postWhisker-isoComp-at π (τ ⁻¹) σ))

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

  normalization : comparison =₂ (target ⁻¹ ∙ source)
  normalization =
    (isoComp-assoc-at ((productMap-comp (id X) h f (id B)) ⁻¹)
      ((productMap-cong (comp-unitʳ h) (comp-unitˡ f)) ⁻¹) source ∙
      isoComp-cong (inverse-composite (productMap-cong (comp-unitʳ h) (comp-unitˡ f))
        (productMap-comp (id X) h f (id B))) (idIso source)) ⁻¹

  sourceFirst = pair-β₁ (h ∘ pr₁) (id A ∘ pr₂) ∙ (comp-unitˡ pr₁ ▷ HA)
  sourceSecond = (f ◁ (comp-unitˡ pr₂ ∙ pair-β₂ (h ∘ pr₁) (id A ∘ pr₂))) ∙ comp-assoc HA pr₂ f
  targetFirst = (h ◁ (comp-unitˡ pr₁ ∙ pair-β₁ (id X ∘ pr₁) (f ∘ pr₂))) ∙ comp-assoc LX pr₁ h
  targetSecond = pair-β₂ (id X ∘ pr₁) (f ∘ pr₂) ∙ (comp-unitˡ pr₂ ▷ LX)
  sourceTail₁ = (pair-β₁ (id Y ∘ pr₁) (f ∘ pr₂) ▷ HA) ∙ (comp-assoc HA LY pr₁) ⁻¹
  sourceTail₂ = (pair-β₂ (id Y ∘ pr₁) (f ∘ pr₂) ▷ HA) ∙ (comp-assoc HA LY pr₂) ⁻¹
  targetTail₁ = (pair-β₁ (h ∘ pr₁) (id B ∘ pr₂) ▷ LX) ∙ (comp-assoc LX HB pr₁) ⁻¹
  targetTail₂ = (pair-β₂ (h ∘ pr₁) (id B ∘ pr₂) ▷ LX) ∙ (comp-assoc LX HB pr₂) ⁻¹
  sourceProjection₁ = sourceFirst ∙ sourceTail₁
  sourceProjection₂ = sourceSecond ∙ sourceTail₂
  targetProjection₁ = targetFirst ∙ targetTail₁
  targetProjection₂ = targetSecond ∙ targetTail₂

  source₁ : (pair-β₁ (h ∘ pr₁) (f ∘ pr₂) ∙ (pr₁ ◁ source)) =₂ sourceProjection₁
  source₁ = isoComp-cong
    (coordinate-left-unit pr₁ h pr₁ HA (pair-β₁ (h ∘ pr₁) (id A ∘ pr₂)))
    (idIso sourceTail₁) ∙ Source.projection₁

  source₂ : (pair-β₂ (h ∘ pr₁) (f ∘ pr₂) ∙ (pr₂ ◁ source)) =₂ sourceProjection₂
  source₂ = isoComp-cong
    (coordinate-inner-unit pr₂ pr₂ HA (pair-β₂ (h ∘ pr₁) (id A ∘ pr₂)) f)
    (idIso sourceTail₂) ∙ Source.projection₂

  target₁ : (pair-β₁ (h ∘ pr₁) (f ∘ pr₂) ∙ (pr₁ ◁ target)) =₂ targetProjection₁
  target₁ = isoComp-cong
    (coordinate-inner-unit pr₁ pr₁ LX (pair-β₁ (id X ∘ pr₁) (f ∘ pr₂)) h)
    (idIso targetTail₁) ∙ Target.projection₁

  target₂ : (pair-β₂ (h ∘ pr₁) (f ∘ pr₂) ∙ (pr₂ ◁ target)) =₂ targetProjection₂
  target₂ = isoComp-cong
    (coordinate-left-unit pr₂ f pr₂ LX (pair-β₂ (id X ∘ pr₁) (f ∘ pr₂)))
    (idIso targetTail₂) ∙ Target.projection₂

  abstract
    projection₁ : (targetProjection₁ ∙ (pr₁ ◁ comparison)) =₂ sourceProjection₁
    projection₁ = source₁ ∙
      (quotient-projection pr₁ (pair-β₁ (h ∘ pr₁) (f ∘ pr₂)) source target ∙
        isoComp-cong (target₁ ⁻¹) (postWhisker pr₁ ◁ normalization))

    projection₂ : (targetProjection₂ ∙ (pr₂ ◁ comparison)) =₂ sourceProjection₂
    projection₂ = source₂ ∙
      (quotient-projection pr₂ (pair-β₂ (h ∘ pr₁) (f ∘ pr₂)) source target ∙
        isoComp-cong (target₂ ⁻¹) (postWhisker pr₂ ◁ normalization))
```
