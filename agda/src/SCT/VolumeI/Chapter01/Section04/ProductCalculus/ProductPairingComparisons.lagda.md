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
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductPairing as ProductPairing

module SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductPairingComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯
  using (Square; compose-square; inverse-square)
open ProductPairing.ChosenComparisons vocabulary terminal products productLaws composition vertical whiskering
  pentagonTriangle public using (module ProductPair; identity-coordinate)

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
