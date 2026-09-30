# Normalizing a matching along a retraction

A matching into the image of a section can be adjusted to have any
prescribed image under its retraction. The adjustment retains both legs
and supplies the equation for its image. No embedding or uniqueness of
matching identifications is assumed in this calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.SplitRetractionMatching
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
  using (post-square)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionRestriction 𝒯
  using (restricted-normalization)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯
  using (post-inverse)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering
  using (substitution-square-projection; project-composite; pre-square-projection)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural
  vocabulary terminal products productLaws composition whiskering
  using (postWhisker-id-at)

module WithRetraction {A B : CAT} (i : MAP A B) (r : MAP B A)
  (ρ : (r ∘ i) =₁ id A) where

  frame : {Γ : CAT} (v : MAP Γ A) → (r ∘ (i ∘ v)) =₁ v
  frame v = comp-unitˡ v ∙ ((ρ ▷ v) ∙ (comp-assoc v i r) ⁻¹)

  abstract
    precompose-image : {Γ : CAT} {G H : MAP Γ B} {v : MAP Γ A}
      (ω : H =₁ (i ∘ v)) (δ : G =₁ H) (p : (r ∘ G) =₁ v) →
      (frame v ∙ (r ◁ ω)) =₂ (p ∙ (r ◁ δ) ⁻¹) →
      (frame v ∙ (r ◁ (ω ∙ δ))) =₂ p
    precompose-image {v = v} ω δ p image = isoComp-unitʳ-at p ∙
      (isoComp-cong (idIso p) (isoComp-inverseˡ-at (r ◁ δ)) ∙
      (isoComp-assoc-at p ((r ◁ δ) ⁻¹) (r ◁ δ) ∙
      (isoComp-cong image (idIso (r ◁ δ)) ∙ project-composite r ω δ (frame v))))

    frame-natural : {Γ : CAT} {v w : MAP Γ A} (χ : v =₁ w) →
      (frame w ∙ (r ◁ (i ◁ χ))) =₂ (χ ∙ frame v)
    frame-natural {v = v} {w} χ = paste-squares
      ((ρ ▷ v) ∙ (comp-assoc v i r) ⁻¹)
      ((ρ ▷ w) ∙ (comp-assoc w i r) ⁻¹)
      (comp-unitˡ v) (comp-unitˡ w)
      (r ◁ (i ◁ χ)) (id A ◁ χ) χ
      (substitution-square-projection r i (id A) ρ χ)
      (postWhisker-id-at χ)

    frame-restrict : {Γ Δ : CAT} (v : MAP Γ A) (t : MAP Δ Γ) →
      (frame (v ∘ t) ∙ (r ◁ comp-assoc t v i)) =₂
      transport-pre r (i ∘ v) (frame v) t
    frame-restrict v t =
      isoComp-cong ((preWhisker-isoComp-at (comp-unitˡ v) (transport-pre r i ρ v) t) ⁻¹)
        (idIso outer) ∙
      (isoComp-cong (isoComp-cong (left-unitor-comp t v) (idIso inner)) (idIso outer) ∙
      (isoComp-cong ((isoComp-assoc-at unit assoc inner) ⁻¹) (idIso outer) ∙
      ((isoComp-assoc-at unit (assoc ∙ inner) outer) ⁻¹ ∙
      (isoComp-cong (idIso unit) ((transport-pre-assoc r i (id A) ρ v t) ⁻¹) ∙
        isoComp-assoc-at unit (transport-pre r i ρ (v ∘ t)) (r ◁ comp-assoc t v i)))))
      where
      unit : (id A ∘ (v ∘ t)) =₁ (v ∘ t)
      unit = comp-unitˡ (v ∘ t)
      assoc : ((id A ∘ v) ∘ t) =₁ (id A ∘ (v ∘ t))
      assoc = comp-assoc t v (id A)
      outer : (r ∘ ((i ∘ v) ∘ t)) =₁ ((r ∘ (i ∘ v)) ∘ t)
      outer = (comp-assoc t (i ∘ v) r) ⁻¹
      inner : ((r ∘ (i ∘ v)) ∘ t) =₁ ((id A ∘ v) ∘ t)
      inner = transport-pre r i ρ v ▷ t

    image-restrict : {Γ Δ : CAT} {H : MAP Γ B} {v : MAP Γ A}
      (ω : H =₁ (i ∘ v)) (p : (r ∘ H) =₁ v) (t : MAP Δ Γ) →
      (frame v ∙ (r ◁ ω)) =₂ p →
      (frame (v ∘ t) ∙ (r ◁ (comp-assoc t v i ∙ (ω ▷ t)))) =₂
      transport-pre r H p t
    image-restrict {H = H} {v} ω p t image =
      isoComp-unitˡ-at (transport-pre r H p t) ∙
      (isoComp-cong (preWhisker-idIso v t) (idIso (transport-pre r H p t)) ∙
      (pre-square-projection r ω (idIso v) p (frame v) t
        ((isoComp-unitˡ-at p) ⁻¹ ∙ image) ∙
      (isoComp-cong (frame-restrict v t) (idIso (r ◁ (ω ▷ t))) ∙
        project-composite r (comp-assoc t v i) (ω ▷ t) (frame (v ∘ t)))))

    image-nested-restrict : {Γ Δ X : CAT} (F : MAP X B) (h : MAP Γ X)
      {v : MAP Γ A} (ω : (F ∘ h) =₁ (i ∘ v))
      (p : (r ∘ (F ∘ h)) =₁ v) (t : MAP Δ Γ) →
      (frame v ∙ (r ◁ ω)) =₂ p →
      (frame (v ∘ t) ∙
        (r ◁ (comp-assoc t v i ∙ ((ω ▷ t) ∙ (comp-assoc t h F) ⁻¹)))) =₂
      restricted-normalization r F h p t
    image-nested-restrict F h {v} ω p t image =
      isoComp-cong (idIso (transport-pre r (F ∘ h) p t)) (post-inverse r (comp-assoc t h F)) ∙
      (isoComp-cong (image-restrict ω p t image) (idIso (r ◁ (comp-assoc t h F) ⁻¹)) ∙
      (project-composite r (comp-assoc t v i ∙ (ω ▷ t))
        ((comp-assoc t h F) ⁻¹) (frame (v ∘ t)) ∙
      isoComp-cong (idIso (frame (v ∘ t)))
        (postWhisker r ◁ (isoComp-assoc-at (comp-assoc t v i) (ω ▷ t)
          ((comp-assoc t h F) ⁻¹)) ⁻¹)))

    image-two-step-restrict : {Γ Δ X Y : CAT} (F : MAP Y B)
      (n : MAP X Y) (k : MAP Γ X) {v : MAP Γ A}
      (ω : (F ∘ (n ∘ k)) =₁ (i ∘ v))
      (p : (r ∘ (F ∘ (n ∘ k))) =₁ v) (t : MAP Δ Γ) →
      (frame v ∙ (r ◁ ω)) =₂ p →
      (frame (v ∘ t) ∙
        (r ◁ (comp-assoc t v i ∙ restricted-normalization F n k ω t))) =₂
      (restricted-normalization r F (n ∘ k) p t ∙
        (r ◁ (F ◁ comp-assoc t k n)) ⁻¹)
    image-two-step-restrict F n k {v} ω p t image =
      isoComp-cong (idIso (restricted-normalization r F (n ∘ k) p t))
        (post-inverse r (F ◁ comp-assoc t k n)) ∙
      (isoComp-cong (image-nested-restrict F (n ∘ k) ω p t image)
        (idIso (r ◁ (F ◁ comp-assoc t k n) ⁻¹)) ∙
      (project-composite r
        (comp-assoc t v i ∙ transport-pre F (n ∘ k) ω t)
        ((F ◁ comp-assoc t k n) ⁻¹) (frame (v ∘ t)) ∙
      isoComp-cong (idIso (frame (v ∘ t)))
        (postWhisker r ◁ (isoComp-assoc-at (comp-assoc t v i)
          (transport-pre F (n ∘ k) ω t) ((F ◁ comp-assoc t k n) ⁻¹)) ⁻¹)))

    retract-square : {Γ : CAT} {h k : MAP Γ B} {v w : MAP Γ A}
      (ωL : h =₁ (i ∘ v)) (ωR : k =₁ (i ∘ w))
      (τ : h =₁ k) (δ : v =₁ w)
      (p : (r ∘ h) =₁ v) (q : (r ∘ k) =₁ w) →
      (ωR ∙ τ) =₂ ((i ◁ δ) ∙ ωL) →
      (frame v ∙ (r ◁ ωL)) =₂ p → (frame w ∙ (r ◁ ωR)) =₂ q →
      (q ∙ (r ◁ τ)) =₂ (δ ∙ p)
    retract-square {v = v} {w} ωL ωR τ δ p q square imageL imageR =
      isoComp-cong (idIso δ) imageL ∙
      (paste-squares (r ◁ ωL) (r ◁ ωR) (frame v) (frame w)
        (r ◁ τ) (r ◁ (i ◁ δ)) δ
        (post-square r ωL ωR τ (i ◁ δ) square) (frame-natural δ) ∙
        isoComp-cong (imageR ⁻¹) (idIso (r ◁ τ)))

  module Normalize {Γ : CAT} {H : MAP Γ B} {v : MAP Γ A}
    (ω : H =₁ (i ∘ v)) (p : (r ∘ H) =₁ v) where

    image : (r ∘ H) =₁ v
    image = frame v ∙ (r ◁ ω)

    correction : v =₁ v
    correction = p ∙ image ⁻¹

    matching : H =₁ (i ∘ v)
    matching = (i ◁ correction) ∙ ω

    abstract
      image-law : (frame v ∙ (r ◁ matching)) =₂ p
      image-law = isoComp-unitʳ-at p ∙
        (isoComp-cong (idIso p) (isoComp-inverseˡ-at image) ∙
        (isoComp-assoc-at p (image ⁻¹) image ∙
        (isoComp-assoc-at correction (frame v) (r ◁ ω) ∙
        (isoComp-cong (frame-natural correction) (idIso (r ◁ ω)) ∙
          project-composite r (i ◁ correction) ω (frame v)))))
```
