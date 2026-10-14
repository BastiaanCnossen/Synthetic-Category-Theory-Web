# Transporting the anima of square witnesses

Transporting a commutative square changes its four corners by specified
identifications. For fixed boundaries this is an equivalence of the
animae of compatibility witnesses. Lifting through that equivalence
recovers a witness together with a computation one dimension higher.
This does not identify this transformation with an independently chosen
square-transport calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.SquareTransport
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
  using (changeEndpoints; changeEndpoints-map; changeEndpoints-map-isEquiv; changeEndpoints-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module At {X Y : CAT} {a₀ a₁ b₀ b₁ x₀ x₁ y₀ y₁ : MAP X Y}
  (L₀ : a₀ =₁ x₀) (L₁ : a₁ =₁ x₁)
  (R₀ : b₀ =₁ y₀) (R₁ : b₁ =₁ y₁)
  (q₀ : a₀ =₁ b₀) (q₁ : a₁ =₁ b₁)
  (u : a₀ =₁ a₁) (v : b₀ =₁ b₁)
  (α : x₀ =₁ x₁) (β : y₀ =₁ y₁)
  (left : (L₁ ∙ u) =₂ (α ∙ L₀))
  (right : (R₁ ∙ v) =₂ (β ∙ R₀)) where

  before-left = q₁ ∙ u
  before-right = v ∙ q₀
  after-left = (R₁ ∙ (q₁ ∙ L₁ ⁻¹)) ∙ α
  after-right = β ∙ (R₀ ∙ (q₀ ∙ L₀ ⁻¹))
  conjugation = changeEndpoints-map L₀ R₁
  conjugation-isEquiv = changeEndpoints-map-isEquiv L₀ R₁

  abstract
    left-frame : (conjugation ∘ before-left) =₂ after-left
    left-frame =
      (isoComp-assoc-at R₁ (q₁ ∙ L₁ ⁻¹) α) ⁻¹ ∙
      (isoComp-cong (idIso R₁) ((isoComp-assoc-at q₁ (L₁ ⁻¹) α) ⁻¹) ∙
      (isoComp-cong (idIso R₁) (isoComp-cong (idIso q₁)
        ((move-square L₁ u α L₀ left) ⁻¹)) ∙
      (isoComp-cong (idIso R₁) (isoComp-assoc-at q₁ u (L₀ ⁻¹)) ∙
        changeEndpoints-at L₀ R₁ before-left)))
    right-frame : (conjugation ∘ before-right) =₂ after-right
    right-frame = isoComp-assoc-at β R₀ (q₀ ∙ L₀ ⁻¹) ∙
      (isoComp-cong right (idIso (q₀ ∙ L₀ ⁻¹)) ∙
      ((isoComp-assoc-at R₁ v (q₀ ∙ L₀ ⁻¹)) ⁻¹ ∙
      (isoComp-cong (idIso R₁) (isoComp-assoc-at v q₀ (L₀ ⁻¹)) ∙
        changeEndpoints-at L₀ R₁ before-right)))

  forward : MAP (before-left ＝ before-right) (after-left ＝ after-right)
  forward = changeEndpoints-map left-frame right-frame ∘ postWhisker conjugation
  forward-isEquiv : IsEquiv forward
  forward-isEquiv = equiv-compose (postWhisker conjugation)
    (changeEndpoints-map left-frame right-frame)
    (postWhisker-isEquiv conjugation conjugation-isEquiv before-left before-right)
    (changeEndpoints-map-isEquiv left-frame right-frame)

  apply : before-left =₂ before-right → after-left =₂ after-right
  apply ζ = forward ∘ ζ
  formula : (ζ : before-left =₂ before-right) → apply ζ =₃
    changeEndpoints left-frame right-frame (conjugation ◁ ζ)
  formula ζ = changeEndpoints-at left-frame right-frame (conjugation ◁ ζ) ∙
    comp-assoc ζ (postWhisker conjugation) (changeEndpoints-map left-frame right-frame)

  module Recover (ζ : after-left =₂ after-right) where
    private
      chosen = equiv-lift forward-isEquiv ζ
    witness : before-left =₂ before-right
    witness = FunctorLift.lift chosen
    computation : apply witness =₃ ζ
    computation = FunctorLift.comparison chosen

  opaque
    recover-apply : (ζ : before-left =₂ before-right) → Recover.witness (apply ζ) =₃ ζ
    recover-apply ζ = equiv-reflect forward-isEquiv (Recover.witness (apply ζ)) ζ
      (Recover.computation (apply ζ))

    recover-congruence : {ζ ζ′ : after-left =₂ after-right} → ζ =₃ ζ′ →
      Recover.witness ζ =₃ Recover.witness ζ′
    recover-congruence {ζ} {ζ′} γ = equiv-reflect forward-isEquiv
      (Recover.witness ζ) (Recover.witness ζ′)
      ((Recover.computation ζ′) ⁻¹ ∙ (γ ∙ Recover.computation ζ))
```
