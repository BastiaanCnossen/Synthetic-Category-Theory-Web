# Pairing maps of cospans

Maps from one cospan to two target cospans combine into a map to their
product. The matching squares are the specified squares of `PairedSquares`.
The image of a cone agrees with the paired component images as a whole
cone, including its matching identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.PairedMaps
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse)
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductCones as Products
import SCT.VolumeI.Chapter01.Section06.Cospans.PairedSquares as Squares
import SCT.VolumeI.Chapter01.Section06.Cospans.ProjectedImages as Images

module Pair {C D E C₀ D₀ E₀ C₁ D₁ E₁ : CAT}
  {f : MAP C E} {g : MAP D E}
  {f₀ : MAP C₀ E₀} {g₀ : MAP D₀ E₀} {f₁ : MAP C₁ E₁} {g₁ : MAP D₁ E₁}
  (H₀ : CospanMap f g f₀ g₀) (H₁ : CospanMap f g f₁ g₁) where
  private
    module H₀ = CospanMap H₀
    module H₁ = CospanMap H₁
    module Left = Squares.Pair 𝒯 f f₀ f₁ H₀.left H₁.left H₀.base H₁.base
      H₀.leftSquare H₁.leftSquare using (matching; first-coordinate; second-coordinate)
    module Right = Squares.Pair 𝒯 g g₀ g₁ H₀.right H₁.right H₀.base H₁.base
      H₀.rightSquare H₁.rightSquare using (matching; first-coordinate; second-coordinate)
    module Product = Products.Coordinates 𝒯 f₀ f₁ g₀ g₁ using (module Paired; module First; module Second; reflect)

  cospan : CospanMap f g (productMap f₀ f₁) (productMap g₀ g₁)
  cospan = record
    { left = pair H₀.left H₁.left ; right = pair H₀.right H₁.right
    ; base = pair H₀.base H₁.base
    ; leftSquare = Left.matching ; rightSquare = Right.matching }

  private
    module First = Images.Coordinate 𝒯 P cospan H₀ pr₁ pr₁ pr₁
      (pair-β₁ (f₀ ∘ pr₁) (f₁ ∘ pr₂)) (pair-β₁ (g₀ ∘ pr₁) (g₁ ∘ pr₂))
      (pair-β₁ H₀.left H₁.left) (pair-β₁ H₀.right H₁.right) (pair-β₁ H₀.base H₁.base)
      using (module At)
    module Second = Images.Coordinate 𝒯 P cospan H₁ pr₂ pr₂ pr₂
      (pair-β₂ (f₀ ∘ pr₁) (f₁ ∘ pr₂)) (pair-β₂ (g₀ ∘ pr₁) (g₁ ∘ pr₂))
      (pair-β₂ H₀.left H₁.left) (pair-β₂ H₀.right H₁.right) (pair-β₂ H₀.base H₁.base)
      using (module At)

  first-comparison : {T : CAT} (s : Cone f g T) →
    ConeIso (Product.First.read (CospanMap.mapCone cospan s)) (H₀.mapCone s)
  first-comparison s = First.At.comparison Left.first-coordinate Right.first-coordinate s

  second-comparison : {T : CAT} (s : Cone f g T) →
    ConeIso (Product.Second.read (CospanMap.mapCone cospan s)) (H₁.mapCone s)
  second-comparison s = Second.At.comparison Left.second-coordinate Right.second-coordinate s

  comparison : {T : CAT} (s : Cone f g T) →
    ConeIso (CospanMap.mapCone cospan s) (Product.Paired.cone (H₀.mapCone s) (H₁.mapCone s))
  comparison s = Product.reflect
    (coneIso-compose (coneIso-inverse (Product.Paired.first (H₀.mapCone s) (H₁.mapCone s)))
      (first-comparison s))
    (coneIso-compose (coneIso-inverse (Product.Paired.second (H₀.mapCone s) (H₁.mapCone s)))
      (second-comparison s))
```
