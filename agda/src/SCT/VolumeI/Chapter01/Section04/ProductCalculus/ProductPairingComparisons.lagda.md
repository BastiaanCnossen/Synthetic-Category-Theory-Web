# Product comparisons with specified coordinates

A comparison into a chosen pair comes with its two projection equations.
The same equations survive taking a quotient of two comparisons. This is
used for object insertion: both routes are compared with the same pair,
and their quotient is the specified insertion square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductPairingComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯
  using (Square; compose-square; inverse-square)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂; left-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)

module ProductPair {X A B C D : CAT}
  (f : MAP A C) (g : MAP B D) (u : MAP X A) (v : MAP X B)
  {u′ : MAP X C} {v′ : MAP X D}
  (α : (f ∘ u) =₁ u′) (β : (g ∘ v) =₁ v′) where

  comparison = pair-cong α β ∙ productMap-pair f g u v
  first = α ∙ ((f ◁ pair-β₁ u v) ∙ comp-assoc (pair u v) pr₁ f)
  second = β ∙ ((g ◁ pair-β₂ u v) ∙ comp-assoc (pair u v) pr₂ g)
  normalized = pair-cong first second ∙ pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u v)

  abstract
    normalization : comparison =₂ normalized
    normalization = isoComp-cong
      ((pair-cong-comp α ((f ◁ pair-β₁ u v) ∙ comp-assoc (pair u v) pr₁ f)
        β ((g ◁ pair-β₂ u v) ∙ comp-assoc (pair u v) pr₂ g)) ⁻¹)
      (idIso (pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u v))) ∙
      (isoComp-assoc-at (pair-cong α β) _ _) ⁻¹

    projection₁ :
      (pair-β₁ u′ v′ ∙ (pr₁ ◁ comparison)) =₂
      (first ∙ ((pair-β₁ (f ∘ pr₁) (g ∘ pr₂) ▷ pair u v) ∙
        (comp-assoc (pair u v) (productMap f g) pr₁) ⁻¹))
    projection₁ = pair-pre-cong-triangle₁ (f ∘ pr₁) (g ∘ pr₂) (pair u v) first second ∙
      isoComp-cong (idIso (pair-β₁ u′ v′)) (postWhisker pr₁ ◁ normalization)

    projection₂ :
      (pair-β₂ u′ v′ ∙ (pr₂ ◁ comparison)) =₂
      (second ∙ ((pair-β₂ (f ∘ pr₁) (g ∘ pr₂) ▷ pair u v) ∙
        (comp-assoc (pair u v) (productMap f g) pr₂) ⁻¹))
    projection₂ = pair-pre-cong-triangle₂ (f ∘ pr₁) (g ∘ pr₂) (pair u v) first second ∙
      isoComp-cong (idIso (pair-β₂ u′ v′)) (postWhisker pr₂ ◁ normalization)

abstract
  quotient-projection : {X Y B : CAT} (π : MAP Y B)
    {a b z : MAP X Y} {q : MAP X B}
    (at-a : (π ∘ a) =₁ q) (at-b : (π ∘ b) =₁ q) (at-z : (π ∘ z) =₁ q)
    (left : a =₁ z) (right : b =₁ z)
    → Square π at-a at-z left → Square π at-b at-z right
    → Square π at-a at-b (right ⁻¹ ∙ left)
  quotient-projection π at-a at-b at-z left right left-square right-square =
    compose-square π at-a at-z at-b (right ⁻¹) left
      (inverse-square π at-b at-z right right-square) left-square
```


The unit in an unchanged coordinate can be absorbed into its projection
witness. This is the normalization used when pasting insertion squares.

```agda
abstract
  identity-coordinate : {X Y A : CAT} (π : MAP Y A) (t : MAP X Y)
    {q : MAP X A} (b : (π ∘ t) =₁ q) →
    (comp-unitˡ q ∙ ((id A ◁ b) ∙ comp-assoc t π (id A))) =₂
      (b ∙ (comp-unitˡ π ▷ t))
  identity-coordinate π t b = isoComp-cong (idIso b) (left-unitor-comp t π) ∙
    (isoComp-assoc-at b (comp-unitˡ (π ∘ t)) (comp-assoc t π (id _)) ∙
    (isoComp-cong (postWhisker-id-at b) (idIso (comp-assoc t π (id _))) ∙
      (isoComp-assoc-at (comp-unitˡ _) (id _ ◁ b) (comp-assoc t π (id _))) ⁻¹))

```
