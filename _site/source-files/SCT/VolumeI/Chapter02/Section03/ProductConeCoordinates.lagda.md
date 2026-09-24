# The two coordinates of a product cone

Pairing two cones preserves their matching data. Conversely, the two
coordinate comparisons reconstruct a comparison of the entire cone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter02.Section03.ProductConeCoordinates
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ComparisonSquares 𝒯
open import SCT.VolumeI.Chapter02.Section03.ProjectedCones 𝒯
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)

module Coordinates {A₀ A₁ B₀ B₁ E₀ E₁ : CAT}
  (f₀ : MAP A₀ E₀) (f₁ : MAP A₁ E₁) (g₀ : MAP B₀ E₀) (g₁ : MAP B₁ E₁) where

  F = productMap f₀ f₁
  G = productMap g₀ g₁
  module First = Coordinate F G f₀ g₀ pr₁ pr₁ pr₁
    (pair-β₁ (f₀ ∘ pr₁) (f₁ ∘ pr₂)) (pair-β₁ (g₀ ∘ pr₁) (g₁ ∘ pr₂))
  module Second = Coordinate F G f₁ g₁ pr₂ pr₂ pr₂
    (pair-β₂ (f₀ ∘ pr₁) (f₁ ∘ pr₂)) (pair-β₂ (g₀ ∘ pr₁) (g₁ ∘ pr₂))

  module Paired {T : CAT} (s₀ : Cone f₀ g₀ T) (s₁ : Cone f₁ g₁ T) where
    p = pair (Cone.left s₀) (Cone.left s₁)
    q = pair (Cone.right s₀) (Cone.right s₁)
    l₀ = pair-β₁ (Cone.left s₀) (Cone.left s₁)
    l₁ = pair-β₂ (Cone.left s₀) (Cone.left s₁)
    r₀ = pair-β₁ (Cone.right s₀) (Cone.right s₁)
    r₁ = pair-β₂ (Cone.right s₀) (Cone.right s₁)
    δ₀ = (g₀ ◁ r₀) ⁻¹ ∙ (Cone.match s₀ ∙ (f₀ ◁ l₀))
    δ₁ = (g₁ ◁ r₁) ⁻¹ ∙ (Cone.match s₁ ∙ (f₁ ◁ l₁))
    ε₀ = (First.right-normal q) ⁻¹ ∙ (δ₀ ∙ First.left-normal p)
    ε₁ = (Second.right-normal q) ⁻¹ ∙ (δ₁ ∙ Second.left-normal p)

    cone : Cone F G T
    cone = record { left = p ; right = q ; match = pair-iso ε₀ ε₁ }

    first-match : (Cone.match (First.read cone)) =₂ δ₀
    first-match = decode-encode (First.left-normal p) (First.right-normal q) δ₀ ∙
      isoComp-cong (idIso (First.right-normal q))
        (isoComp-cong (pair-iso-β₁ ε₀ ε₁) (idIso ((First.left-normal p) ⁻¹)))
    second-match : (Cone.match (Second.read cone)) =₂ δ₁
    second-match = decode-encode (Second.left-normal p) (Second.right-normal q) δ₁ ∙
      isoComp-cong (idIso (Second.right-normal q))
        (isoComp-cong (pair-iso-β₂ ε₀ ε₁) (idIso ((Second.left-normal p) ⁻¹)))

    first : ConeIso (First.read cone) s₀
    first = record { leftIso = l₀ ; rightIso = r₀
      ; compatible = isoComp-cong (idIso (g₀ ◁ r₀)) (first-match ⁻¹) ∙
          (cancel-inverse (g₀ ◁ r₀) (Cone.match s₀ ∙ (f₀ ◁ l₀))) ⁻¹ }
    second : ConeIso (Second.read cone) s₁
    second = record { leftIso = l₁ ; rightIso = r₁
      ; compatible = isoComp-cong (idIso (g₁ ◁ r₁)) (second-match ⁻¹) ∙
          (cancel-inverse (g₁ ◁ r₁) (Cone.match s₁ ∙ (f₁ ◁ l₁))) ⁻¹ }

  reflect : {T : CAT} {s t : Cone F G T} →
    ConeIso (First.read s) (First.read t) →
    ConeIso (Second.read s) (Second.read t) → ConeIso s t
  reflect {s = s} {t} Φ Ψ = record
    { leftIso = L ; rightIso = R
    ; compatible = pair-iso-extensionality first-square second-square }
    where
    L = pair-iso (ConeIso.leftIso Φ) (ConeIso.leftIso Ψ)
    R = pair-iso (ConeIso.rightIso Φ) (ConeIso.rightIso Ψ)
    left₀ = pair-iso-β₁ (ConeIso.leftIso Φ) (ConeIso.leftIso Ψ)
    left₁ = pair-iso-β₂ (ConeIso.leftIso Φ) (ConeIso.leftIso Ψ)
    right₀ = pair-iso-β₁ (ConeIso.rightIso Φ) (ConeIso.rightIso Ψ)
    right₁ = pair-iso-β₂ (ConeIso.rightIso Φ) (ConeIso.rightIso Ψ)
    first-square = (postWhisker-isoComp-at pr₁ (G ◁ R) (Cone.match s)) ⁻¹ ∙
      (reflect-transport-square
        (First.left-normal (Cone.left s)) (First.left-normal (Cone.left t))
        (First.right-normal (Cone.right s)) (First.right-normal (Cone.right t))
        (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t) (pr₁ ◁ (F ◁ L)) (pr₁ ◁ (G ◁ R))
        (f₀ ◁ (pr₁ ◁ L)) (g₀ ◁ (pr₁ ◁ R)) (First.left-natural L) (First.right-natural R)
        (isoComp-cong (postWhisker g₀ ◁ right₀ ⁻¹) (idIso (Cone.match (First.read s))) ∙
          (ConeIso.compatible Φ ∙ isoComp-cong (idIso (Cone.match (First.read t))) (postWhisker f₀ ◁ left₀))) ∙
        postWhisker-isoComp-at pr₁ (Cone.match t) (F ◁ L))
    second-square = (postWhisker-isoComp-at pr₂ (G ◁ R) (Cone.match s)) ⁻¹ ∙
      (reflect-transport-square
        (Second.left-normal (Cone.left s)) (Second.left-normal (Cone.left t))
        (Second.right-normal (Cone.right s)) (Second.right-normal (Cone.right t))
        (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t) (pr₂ ◁ (F ◁ L)) (pr₂ ◁ (G ◁ R))
        (f₁ ◁ (pr₂ ◁ L)) (g₁ ◁ (pr₂ ◁ R)) (Second.left-natural L) (Second.right-natural R)
        (isoComp-cong (postWhisker g₁ ◁ right₁ ⁻¹) (idIso (Cone.match (Second.read s))) ∙
          (ConeIso.compatible Ψ ∙ isoComp-cong (idIso (Cone.match (Second.read t))) (postWhisker f₁ ◁ left₁))) ∙
        postWhisker-isoComp-at pr₂ (Cone.match t) (F ◁ L))
```
