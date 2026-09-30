# Pairing specified squares

Two squares with the same source arrow give a square into the product
of their target arrows. We choose its matching with `pair-iso`, retaining
the two component matchings through explicit coordinate computations.
This is a new specified construction; no equality with a differently
parenthesized product comparison is asserted.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section06.Cospans.PairedSquares
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (decode-encode)
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductCones as Products
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedSquareRestriction as Restriction

module Pair {C E A₀ A₁ B₀ B₁ : CAT}
  (f : MAP C E) (f₀ : MAP A₀ B₀) (f₁ : MAP A₁ B₁)
  (u₀ : MAP C A₀) (u₁ : MAP C A₁) (w₀ : MAP E B₀) (w₁ : MAP E B₁)
  (α₀ : (f₀ ∘ u₀) =₁ (w₀ ∘ f)) (α₁ : (f₁ ∘ u₁) =₁ (w₁ ∘ f)) where
  private
    module Product = Products.Coordinates 𝒯 f₀ f₁ f₀ f₁ using (module First; module Second)
  F = productMap f₀ f₁
  U = pair u₀ u₁
  W = pair w₀ w₁
  l₀ = (f₀ ◁ pair-β₁ u₀ u₁) ∙ Product.First.left-normal U
  l₁ = (f₁ ◁ pair-β₂ u₀ u₁) ∙ Product.Second.left-normal U
  r₀ = project-pair₁ w₀ w₁ f
  r₁ = project-pair₂ w₀ w₁ f
  ε₀ = r₀ ⁻¹ ∙ (α₀ ∙ l₀)
  ε₁ = r₁ ⁻¹ ∙ (α₁ ∙ l₁)

  matching : (F ∘ U) =₁ (W ∘ f)
  matching = pair-iso ε₀ ε₁
  square : Cone F W C
  square = record { left = U ; right = f ; match = matching }

  first-coordinate : (r₀ ∙ ((pr₁ ◁ matching) ∙ l₀ ⁻¹)) =₂ α₀
  first-coordinate = decode-encode l₀ r₀ α₀ ∙
    isoComp-cong (idIso r₀) (isoComp-cong (pair-iso-β₁ ε₀ ε₁) (idIso (l₀ ⁻¹)))
  second-coordinate : (r₁ ∙ ((pr₂ ◁ matching) ∙ l₁ ⁻¹)) =₂ α₁
  second-coordinate = decode-encode l₁ r₁ α₁ ∙
    isoComp-cong (idIso r₁) (isoComp-cong (pair-iso-β₂ ε₀ ε₁) (idIso (l₁ ⁻¹)))

  private
    module First = Restriction.At 𝒯 F W f pr₁ pr₁ f₀ w₀
      (pair-β₁ (f₀ ∘ pr₁) (f₁ ∘ pr₂)) (pair-β₁ w₀ w₁)
      U u₀ (pair-β₁ u₀ u₁) matching α₀ using (component; module Restrict)
    module Second = Restriction.At 𝒯 F W f pr₂ pr₂ f₁ w₁
      (pair-β₂ (f₀ ∘ pr₁) (f₁ ∘ pr₂)) (pair-β₂ w₀ w₁)
      U u₁ (pair-β₂ u₀ u₁) matching α₁ using (component; module Restrict)

  first-restriction : {T : CAT} (p : MAP T C) →
    (Cone.match (conePre p First.component) ∙
      ((f₀ ◁ project-pair₁ u₀ u₁ p) ∙ Product.First.left-normal (U ∘ p))) =₂
    (project-pair₁ w₀ w₁ (f ∘ p) ∙ (pr₁ ◁ Cone.match (conePre p square)))
  first-restriction p = First.Restrict.comparison first-coordinate p

  second-restriction : {T : CAT} (p : MAP T C) →
    (Cone.match (conePre p Second.component) ∙
      ((f₁ ◁ project-pair₂ u₀ u₁ p) ∙ Product.Second.left-normal (U ∘ p))) =₂
    (project-pair₂ w₀ w₁ (f ∘ p) ∙ (pr₂ ◁ Cone.match (conePre p square)))
  second-restriction p = Second.Restrict.comparison second-coordinate p
```
