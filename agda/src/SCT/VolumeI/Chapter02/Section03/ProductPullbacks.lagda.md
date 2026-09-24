# Products of pullback squares

Pair the two restricted universal cones. Reading either coordinate recovers
its original cone, including the matching. Factorization and comparison
therefore follow separately in the two coordinates, then pair back together.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section03.ProductPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackCriterion 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter02.Section03.ProductConeCoordinates 𝒯

module Product {A₀ A₁ B₀ B₁ E₀ E₁ S₀ S₁ : CAT}
  {f₀ : MAP A₀ E₀} {f₁ : MAP A₁ E₁} {g₀ : MAP B₀ E₀} {g₁ : MAP B₁ E₁}
  (s₀ : Cone f₀ g₀ S₀) (s₁ : Cone f₁ g₁ S₁)
  (e₀ : IsPullback s₀) (e₁ : IsPullback s₁) where

  open Coordinates f₀ f₁ g₀ g₁
  module U₀ = UniversalCone s₀ e₀
  module U₁ = UniversalCone s₁ e₁
  module Pair = Paired (conePre pr₁ s₀) (conePre pr₂ s₁)

  square : Cone F G (S₀ × S₁)
  square = Pair.cone

  first-restriction : {T : CAT} (h : MAP T (S₀ × S₁)) →
    ConeIso (First.read (conePre h square)) (conePre (pr₁ ∘ h) s₀)
  first-restriction h = coneIso-compose (conePre-assoc h pr₁ s₀)
    (coneIso-compose (coneIso-pre h Pair.first) (First.read-pre h square))

  second-restriction : {T : CAT} (h : MAP T (S₀ × S₁)) →
    ConeIso (Second.read (conePre h square)) (conePre (pr₂ ∘ h) s₁)
  second-restriction h = coneIso-compose (conePre-assoc h pr₂ s₁)
    (coneIso-compose (coneIso-pre h Pair.second) (Second.read-pre h square))

  target = pullbackCone F G
  factor₀ = U₀.factor (First.read target)
  factor₁ = U₁.factor (Second.read target)
  inverse = pair factor₀ factor₁

  factorization : ConeIso (conePre inverse square) target
  factorization = reflect
    (coneIso-compose (U₀.factor-β (First.read target))
      (coneIso-compose (cone-action s₀ (pair-β₁ factor₀ factor₁)) (first-restriction inverse)))
    (coneIso-compose (U₁.factor-β (Second.read target))
      (coneIso-compose (cone-action s₁ (pair-β₂ factor₀ factor₁)) (second-restriction inverse)))

  reflect-maps : (h k : MAP (S₀ × S₁) (S₀ × S₁)) →
    ConeIso (conePre h square) (conePre k square) → h =₁ k
  reflect-maps h k Φ = pair-iso
    (U₀.reflect (pr₁ ∘ h) (pr₁ ∘ k)
      (coneIso-compose (first-restriction k)
        (coneIso-compose (First.read-iso Φ) (coneIso-inverse (first-restriction h)))))
    (U₁.reflect (pr₂ ∘ h) (pr₂ ∘ k)
      (coneIso-compose (second-restriction k)
        (coneIso-compose (Second.read-iso Φ) (coneIso-inverse (second-restriction h)))))

  opaque
    square-isPullback : IsPullback square
    square-isPullback = cone-isPullback-from-lifting square inverse factorization reflect-maps
```
