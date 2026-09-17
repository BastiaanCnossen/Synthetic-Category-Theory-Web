# Projections of normalized product comparisons

Composing two product maps and then changing their coordinates gives
the same comparison as pairing the two changed coordinate comparisons.
The two projection witnesses below refer to the original chosen composite.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits as ProductUnits

module SCT.VolumeI.Chapter01.Section08.ProductComparisonProjections
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp)
open ProductUnits
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)

module Normalized {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
  (f₀ : MAP A₀ A₁) (f₁ : MAP A₁ A₂) (g₀ : MAP B₀ B₁) (g₁ : MAP B₁ B₂)
  {f : MAP A₀ A₂} {g : MAP B₀ B₂}
  (α : NatIso (f₁ ∘ f₀) f) (β : NatIso (g₁ ∘ g₀) g) where

  input = productMap f₀ g₀
  firstBefore = coordinate-comparison pr₁ f₀ pr₁ input (pair-β₁ (f₀ ∘ pr₁) (g₀ ∘ pr₂)) f₁
  secondBefore = coordinate-comparison pr₂ g₀ pr₂ input (pair-β₂ (f₀ ∘ pr₁) (g₀ ∘ pr₂)) g₁
  first = (α ▷ pr₁) ∙ firstBefore
  second = (β ▷ pr₂) ∙ secondBefore
  value = productMap-cong α β ∙ productMap-comp f₀ f₁ g₀ g₁
  normalized = pair-cong first second ∙ pair-pre (f₁ ∘ pr₁) (g₁ ∘ pr₂) input

  normalization : Iso₂ value normalized
  normalization = isoComp-cong (invIso (pair-cong-comp (α ▷ pr₁) firstBefore (β ▷ pr₂) secondBefore))
      (idIso (pair-pre (f₁ ∘ pr₁) (g₁ ∘ pr₂) input)) ∙
    invIso (isoComp-assoc-at (productMap-cong α β) (pair-cong firstBefore secondBefore)
      (pair-pre (f₁ ∘ pr₁) (g₁ ∘ pr₂) input))

  projection₁ : Iso₂ (pair-β₁ (f ∘ pr₁) (g ∘ pr₂) ∙ (pr₁ ◁ value))
    (first ∙ ((pair-β₁ (f₁ ∘ pr₁) (g₁ ∘ pr₂) ▷ input) ∙
      invIso (comp-assoc input (productMap f₁ g₁) pr₁)))
  projection₁ = pair-pre-cong-triangle₁ (f₁ ∘ pr₁) (g₁ ∘ pr₂) input first second ∙
    isoComp-cong (idIso (pair-β₁ (f ∘ pr₁) (g ∘ pr₂))) (postWhisker pr₁ ◁ normalization)

  projection₂ : Iso₂ (pair-β₂ (f ∘ pr₁) (g ∘ pr₂) ∙ (pr₂ ◁ value))
    (second ∙ ((pair-β₂ (f₁ ∘ pr₁) (g₁ ∘ pr₂) ▷ input) ∙
      invIso (comp-assoc input (productMap f₁ g₁) pr₂)))
  projection₂ = pair-pre-cong-triangle₂ (f₁ ∘ pr₁) (g₁ ∘ pr₂) input first second ∙
    isoComp-cong (idIso (pair-β₂ (f ∘ pr₁) (g ∘ pr₂))) (postWhisker pr₂ ◁ normalization)
```

For a fixed parameter category, the first coordinate reduces to its
projection and unitor. The second coordinate is the ordinary composition
comparison. These are the projection witnesses for `productRestriction-comp`.

```agda
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (coordinate-left-unit)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)

module Restriction {A B C : CAT} (X : CAT) (f : MAP A B) (g : MAP B C) where
  input = productMap (id X) f
  outer = productMap (id X) g
  module N = Normalized (id X) (id X) f g (comp-unitˡ (id X)) (idIso (g ∘ f))
  first = pair-β₁ (id X ∘ pr₁) (f ∘ pr₂) ∙ (comp-unitˡ pr₁ ▷ input)
  second = coordinate-comparison pr₂ f pr₂ input (pair-β₂ (id X ∘ pr₁) (f ∘ pr₂)) g

  projection₁ : Iso₂
    (pair-β₁ (id X ∘ pr₁) ((g ∘ f) ∘ pr₂) ∙ (pr₁ ◁ productRestriction-comp X f g))
    (first ∙ ((pair-β₁ (id X ∘ pr₁) (g ∘ pr₂) ▷ input) ∙ invIso (comp-assoc input outer pr₁)))
  projection₁ = isoComp-cong
    (coordinate-left-unit pr₁ (id X) pr₁ input (pair-β₁ (id X ∘ pr₁) (f ∘ pr₂)))
    (idIso _) ∙ N.projection₁

  projection₂ : Iso₂
    (pair-β₂ (id X ∘ pr₁) ((g ∘ f) ∘ pr₂) ∙ (pr₂ ◁ productRestriction-comp X f g))
    (second ∙ ((pair-β₂ (id X ∘ pr₁) (g ∘ pr₂) ▷ input) ∙ invIso (comp-assoc input outer pr₂)))
  projection₂ = isoComp-cong
    (isoComp-unitˡ-at second ∙ isoComp-cong (preWhisker-idIso (g ∘ f) pr₂) (idIso second))
    (idIso _) ∙ N.projection₂
```
