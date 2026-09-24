# Associativity of composition in both product coordinates

The pasting comparison uses products with a changing second coordinate.
We therefore retain both coordinate associators. The proof reuses the
pairing assembly from Section 1.4; its two projection hypotheses follow
from the specified product comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.ProductCompositionAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.ProductAssociativity 𝒯 M
  using (post-pasting; cancel-forward; module PairingAssembly)
open import SCT.VolumeI.Chapter01.Section04.ProductSubstitution 𝒯 M
  using (coordinate-outer-comp)
open ProductFunctorUnits vocabulary terminal products productLaws composition
  vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at)

module CoordinateAssociativity
  {K₀ K₁ K₂ A₀ A₁ A₂ A₃ : CAT}
  (π₀ : MAP K₀ A₀) (π₁ : MAP K₁ A₁) (π₂ : MAP K₂ A₂)
  (f₀ : MAP A₀ A₁) (f₁ : MAP A₁ A₂) (f₂ : MAP A₂ A₃)
  (h : MAP K₁ K₂) (k : MAP K₀ K₁) (l : MAP K₀ K₂)
  (κ : (h ∘ k) =₁ l)
  (b : (π₂ ∘ h) =₁ (f₁ ∘ π₁))
  (d : (π₁ ∘ k) =₁ (f₀ ∘ π₀))
  (b′ : (π₂ ∘ l) =₁ ((f₁ ∘ f₀) ∘ π₀)) where

  middle : ((f₁ ∘ π₁) ∘ k) =₁ ((f₁ ∘ f₀) ∘ π₀)
  middle = coordinate-comparison π₀ f₀ π₁ k d f₁
  firstStep : ((f₂ ∘ π₂) ∘ h) =₁ ((f₂ ∘ f₁) ∘ π₁)
  firstStep = coordinate-comparison π₁ f₁ π₂ h b f₂
  secondStep : (((f₂ ∘ f₁) ∘ π₁) ∘ k) =₁ (((f₂ ∘ f₁) ∘ f₀) ∘ π₀)
  secondStep = coordinate-comparison π₀ f₀ π₁ k d (f₂ ∘ f₁)
  direct : ((f₂ ∘ π₂) ∘ l) =₁ ((f₂ ∘ (f₁ ∘ f₀)) ∘ π₀)
  direct = coordinate-comparison π₀ (f₁ ∘ f₀) π₂ l b′ f₂
  short : (((f₂ ∘ π₂) ∘ h) ∘ k) =₁ ((f₂ ∘ (f₁ ∘ f₀)) ∘ π₀)
  short = direct ∙ (((f₂ ∘ π₂) ◁ κ) ∙ comp-assoc k h (f₂ ∘ π₂))
  long : (((f₂ ∘ π₂) ∘ h) ∘ k) =₁ ((f₂ ∘ (f₁ ∘ f₀)) ∘ π₀)
  long = (comp-assoc f₀ f₁ f₂ ▷ π₀) ∙ (secondStep ∙ (firstStep ▷ k))

  abstract
    comparison :
      (b′ ∙ (π₂ ◁ κ)) =₂
        (middle ∙ ((b ▷ k) ∙ (comp-assoc k h π₂) ⁻¹)) → short =₂ long
    comparison projection =
      let outside = (comp-assoc π₀ (f₁ ∘ f₀) f₂) ⁻¹
          leftImage = f₂ ◁ b′
          inputA = comp-assoc l π₂ f₂
          change = (f₂ ∘ π₂) ◁ κ
          sourceA = comp-assoc k h (f₂ ∘ π₂)
          across = f₂ ◁ (π₂ ◁ κ)
          afterA = comp-assoc (h ∘ k) π₂ f₂
          projectImage = (postWhisker f₂ ◁ projection) ∙
            (postWhisker-isoComp-at f₂ b′ (π₂ ◁ κ)) ⁻¹
          moveInput = isoComp-assoc-at across afterA sourceA ∙
            (isoComp-cong (postWhisker-comp-at κ π₂ f₂) (idIso sourceA) ∙
              (isoComp-assoc-at inputA change sourceA) ⁻¹)
          removeInner = isoComp-cong projectImage (idIso (afterA ∙ sourceA)) ∙
            (isoComp-assoc-at leftImage across (afterA ∙ sourceA)) ⁻¹
          normalizeShort = isoComp-cong (idIso outside)
            (post-pasting f₂ π₂ h k b middle ∙
              (removeInner ∙
                (isoComp-cong (idIso leftImage) moveInput ∙
                  isoComp-assoc-at leftImage inputA (change ∙ sourceA)))) ∙
            isoComp-assoc-at outside (leftImage ∙ inputA) (change ∙ sourceA)
          η = comp-assoc f₀ f₁ f₂ ▷ π₀
          sourceCorner = comp-assoc π₁ f₁ f₂
          imageBefore = (f₂ ◁ b) ∙ comp-assoc h π₂ f₂
          nextCoordinate = coordinate-comparison π₀ (f₁ ∘ f₀) (f₁ ∘ π₁) k middle f₂
          outerSquare = coordinate-outer-comp π₀ f₀ π₁ k d f₁ f₂
          simplifyCorner = (preWhisker k ◁ cancel-forward sourceCorner imageBefore) ∙
            (preWhisker-isoComp-at sourceCorner firstStep k) ⁻¹
          normalizeLong = isoComp-cong (idIso outside)
            (isoComp-assoc-at (f₂ ◁ middle) (comp-assoc k (f₁ ∘ π₁) f₂) (imageBefore ▷ k)) ∙
            (isoComp-assoc-at outside
              ((f₂ ◁ middle) ∙ comp-assoc k (f₁ ∘ π₁) f₂) (imageBefore ▷ k) ∙
            (isoComp-cong (idIso nextCoordinate) simplifyCorner ∙
            (isoComp-assoc-at nextCoordinate (sourceCorner ▷ k) (firstStep ▷ k) ∙
            (isoComp-cong outerSquare (idIso (firstStep ▷ k)) ∙
              (isoComp-assoc-at η secondStep (firstStep ▷ k)) ⁻¹))))
      in normalizeLong ⁻¹ ∙ normalizeShort

module ProductCompositor
  {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : CAT}
  (f₀ : MAP A₀ A₁) (f₁ : MAP A₁ A₂) (f₂ : MAP A₂ A₃)
  (g₀ : MAP B₀ B₁) (g₁ : MAP B₁ B₂) (g₂ : MAP B₂ B₃) where

  h = productMap f₁ g₁
  k = productMap f₀ g₀
  l = productMap (f₁ ∘ f₀) (g₁ ∘ g₀)
  κ = productMap-comp f₀ f₁ g₀ g₁
  b₁ = pair-β₁ (f₁ ∘ pr₁) (g₁ ∘ pr₂)
  b₂ = pair-β₂ (f₁ ∘ pr₁) (g₁ ∘ pr₂)
  d₁ = pair-β₁ (f₀ ∘ pr₁) (g₀ ∘ pr₂)
  d₂ = pair-β₂ (f₀ ∘ pr₁) (g₀ ∘ pr₂)
  b′₁ = pair-β₁ ((f₁ ∘ f₀) ∘ pr₁) ((g₁ ∘ g₀) ∘ pr₂)
  b′₂ = pair-β₂ ((f₁ ∘ f₀) ∘ pr₁) ((g₁ ∘ g₀) ∘ pr₂)
  module First = CoordinateAssociativity pr₁ pr₁ pr₁ f₀ f₁ f₂ h k l κ b₁ d₁ b′₁
  module Second = CoordinateAssociativity pr₂ pr₂ pr₂ g₀ g₁ g₂ h k l κ b₂ d₂ b′₂

  abstract
    first-coordinate : First.short =₂ First.long
    first-coordinate = First.comparison
      (pair-pre-cong-triangle₁ (f₁ ∘ pr₁) (g₁ ∘ pr₂) k First.middle Second.middle)
    second-coordinate : Second.short =₂ Second.long
    second-coordinate = Second.comparison
      (pair-pre-cong-triangle₂ (f₁ ∘ pr₁) (g₁ ∘ pr₂) k First.middle Second.middle)

    law :
      (productMap-comp (f₁ ∘ f₀) f₂ (g₁ ∘ g₀) g₂ ∙
        ((productMap f₂ g₂ ◁ productMap-comp f₀ f₁ g₀ g₁) ∙
          comp-assoc (productMap f₀ g₀) (productMap f₁ g₁) (productMap f₂ g₂))) =₂
      (productMap-cong (comp-assoc f₀ f₁ f₂) (comp-assoc g₀ g₁ g₂) ∙
        (productMap-comp f₀ (f₂ ∘ f₁) g₀ (g₂ ∘ g₁) ∙
          (productMap-comp f₁ f₂ g₁ g₂ ▷ productMap f₀ g₀)))
    law = PairingAssembly.assemble (f₂ ∘ pr₁) (g₂ ∘ pr₂) h k l κ
      First.firstStep Second.firstStep First.secondStep Second.secondStep
      First.direct Second.direct (comp-assoc f₀ f₁ f₂ ▷ pr₁) (comp-assoc g₀ g₁ g₂ ▷ pr₂)
      first-coordinate second-coordinate
```
