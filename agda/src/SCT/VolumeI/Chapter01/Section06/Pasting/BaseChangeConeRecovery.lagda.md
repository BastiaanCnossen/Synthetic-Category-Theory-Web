# Recovering the outer cone after base change

Mapping the inner base-change square through the original square
recovers the specified outer cone. This is a comparison of whole cones,
not merely of their legs. It exposes the computation of the chosen
base-change inclusion for subsequent maps of fibers.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeConeRecovery
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneIso-swap; coneSwap-pre; coneSwap-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
import SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeSquares as BaseChange
import SCT.VolumeI.Chapter01.Section06.Cospans.FixedParameterConeAction as Map

private
  remove-inverse-units : {A B : CAT} {u v : MAP A B} (α : u =₁ v) →
    ((α ∙ (idIso u) ⁻¹) ∙ (idIso u) ⁻¹) =₂ α
  remove-inverse-units {u = u} α = isoComp-unitʳ-at α ∙
    isoComp-cong (isoComp-unitʳ-at α ∙ isoComp-cong (idIso α) (inverse-identity u)) (inverse-identity u)

  reverse-comparison : {A B C X Y : CAT} {f : MAP A C} {g : MAP B C}
    (h : MAP X Y) (s : Cone f g Y) (t : Cone g f X) →
    (Φ : ConeIso (conePre h (coneSwap s)) t) → ConeIso (conePre h s) (coneSwap t)
  reverse-comparison h s t Φ = coneIso-adjust raw (ConeIso.rightIso Φ) (ConeIso.leftIso Φ)
    (remove-inverse-units (ConeIso.rightIso Φ)) (remove-inverse-units (ConeIso.leftIso Φ))
    where
    raw = coneIso-compose
      (coneIso-swap (coneIso-compose Φ (coneIso-inverse (coneSwap-pre h s))))
      (coneIso-inverse (coneSwap-swap (conePre h s)))

module Along {C D Z Q Γ X : CAT} (p : MAP C Z) (b : MAP D Z)
  (first : Cone p b Q) (ef : IsPullback first) (k : MAP Γ D)
  (outer : Cone p (b ∘ k) X) (eo : IsPullback outer) where
  private
    module Change = BaseChange.Along 𝒯 P p b first ef k (idIso (b ∘ k)) outer eo
      using (factor; factor-cone; factor-computation; square)
    module Image = Map.Along 𝒯 P (Cone.right first) k (Cone.left first) p b (b ∘ k)
      (Cone.match first) (idIso (b ∘ k)) using (cospan; value; module At)
    i = Change.factor
    a₀ = Cone.left outer
    r = Cone.right outer
    τ = Cone.match outer
    leg = ConeIso.rightIso Change.factor-computation
    η = ConeIso.leftIso Change.factor-computation
    R₀ = (idIso (b ∘ k) ▷ r) ∙ (comp-assoc r k b) ⁻¹
    G = Cone.match (conePre i first)
    normalized = Image.value Change.square

    reverted : ConeIso (conePre i first) (coneSwap Change.factor-cone)
    reverted = reverse-comparison i first Change.factor-cone Change.factor-computation

    abstract
      inverse-edge : ((τ ⁻¹ ∙ R₀) ⁻¹) =₂ (R₀ ⁻¹ ∙ τ)
      inverse-edge = isoComp-cong (idIso (R₀ ⁻¹)) (inverse-inverse τ) ∙ inverse-composite (τ ⁻¹) R₀

      cancel-edge : (R₀ ∙ (τ ⁻¹ ∙ R₀) ⁻¹) =₂ τ
      cancel-edge = cancel-inverse R₀ τ ∙ isoComp-cong (idIso R₀) inverse-edge

      matching : Cone.match normalized =₂ (τ ∙ (p ◁ leg))
      matching = isoComp-cong cancel-edge (idIso (p ◁ leg)) ∙
        ((isoComp-assoc-at R₀ ((τ ⁻¹ ∙ R₀) ⁻¹) (p ◁ leg)) ⁻¹ ∙
        (isoComp-cong (idIso R₀) ((ConeIso.compatible reverted) ⁻¹) ∙
          (isoComp-assoc-at (idIso (b ∘ k) ▷ r) ((comp-assoc r k b) ⁻¹) ((b ◁ η) ∙ G)) ⁻¹))

    normalization : ConeIso normalized outer
    normalization = record { leftIso = leg ; rightIso = idIso r
      ; compatible = isoComp-cong ((postWhisker-idIso (b ∘ k) r) ⁻¹) (idIso (Cone.match normalized)) ∙
          ((isoComp-unitˡ-at (Cone.match normalized)) ⁻¹ ∙ matching ⁻¹) }

  cospan = Image.cospan

  comparison : ConeIso (CospanMap.mapCone cospan Change.square) outer
  comparison = coneIso-compose normalization (Image.At.comparison Change.square)
```
