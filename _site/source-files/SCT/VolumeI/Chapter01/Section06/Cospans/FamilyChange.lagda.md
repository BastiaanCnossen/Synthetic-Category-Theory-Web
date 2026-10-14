# Changing the family of a fiber

A specified identification of the family changes a fiber cone by
postcomposing its matching. The usual identity-leg cospan map realizes
this operation. Its comparison below removes the identity functors and
unitors while retaining the complete cone matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.FamilyChange
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (triangle-whiskered)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural
  vocabulary terminal products productLaws composition whiskering using (preWhisker-comp-at)
import SCT.VolumeI.Chapter01.Section06.Cospans.FixedBaseConeAction as Fixed
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Lifting
open Laws.PullbackStructure P

private
  abstract
    identity-leg : {X Y Γ : CAT} (u : MAP X Y) (p : MAP Γ X) →
      ((comp-unitʳ u ▷ p) ∙ (comp-assoc p (id X) u) ⁻¹) =₂ (u ◁ comp-unitˡ p)
    identity-leg u p = cancel-right (comp-assoc p (id _) u) (u ◁ comp-unitˡ p) ∙
      isoComp-cong (triangle-whiskered p u) (idIso ((comp-assoc p (id _) u) ⁻¹))

module Change {C D B : CAT} (u : MAP C D) {a a′ : MAP B D} (θ : a =₁ a′) where
  private
    module FixedChange = Fixed.Fixed 𝒯 P (id C) (id B)
      (comp-unitʳ u) (θ ⁻¹ ∙ comp-unitʳ a′) using (cospan; module At)
  cospan : CospanMap u a u a′
  cospan = FixedChange.cospan
  open CospanMap cospan public using () renaming (pullbackMap to map; pullbackMap-β to map-β)

  value : {Γ : CAT} → Cone u a Γ → Cone u a′ Γ
  value s = record { left = Cone.left s ; right = Cone.right s ; match = (θ ▷ Cone.right s) ∙ Cone.match s }

  module At {Γ : CAT} (s : Cone u a Γ) where
    private
      module Normal = FixedChange.At s using (simplified; comparison; module L; module R)
      p = Cone.left s
      r = Cone.right s
      τ = Cone.match s
      R = Normal.R.forward
      L = Normal.L.forward
      right-boundary = a′ ◁ comp-unitˡ r
      θr = θ ▷ r
      abstract
        right-normal : R =₂ ((θr ⁻¹) ∙ right-boundary)
        right-normal = isoComp-cong (pre-inverse θ r) (identity-leg a′ r) ∙
          (isoComp-assoc-at (θ ⁻¹ ▷ r) (comp-unitʳ a′ ▷ r)
            ((comp-assoc r (id B) a′) ⁻¹) ∙
          isoComp-cong (preWhisker-isoComp-at (θ ⁻¹) (comp-unitʳ a′) r)
            (idIso ((comp-assoc r (id B) a′) ⁻¹)))
        right-triangle : (θr ∙ R) =₂ right-boundary
        right-triangle = cancel-inverse θr right-boundary ∙ isoComp-cong (idIso θr) right-normal
        right-route : θr =₂ (right-boundary ∙ R ⁻¹)
        right-route = isoComp-cong right-triangle (idIso (R ⁻¹)) ∙ (cancel-right R θr) ⁻¹
        matching : (Cone.match (value s) ∙ (u ◁ comp-unitˡ p)) =₂
          (right-boundary ∙ Cone.match Normal.simplified)
        matching = isoComp-assoc-at right-boundary (R ⁻¹) (τ ∙ L) ∙
          (isoComp-cong right-route (idIso (τ ∙ L)) ∙
          (isoComp-cong (idIso θr) (isoComp-cong (idIso τ) ((identity-leg u p) ⁻¹)) ∙
            isoComp-assoc-at θr τ (u ◁ comp-unitˡ p)))
    normalization : ConeIso Normal.simplified (value s)
    normalization = record { leftIso = comp-unitˡ p ; rightIso = comp-unitˡ r ; compatible = matching }
    comparison : ConeIso (CospanMap.mapCone cospan s) (value s)
    comparison = coneIso-compose normalization Normal.comparison

  computation : ConeIso (conePre map (pullbackCone u a′)) (value (pullbackCone u a))
  computation = coneIso-compose (At.comparison (pullbackCone u a)) map-β

  action : {Γ : CAT} {s t : Cone u a Γ} → ConeIso s t → ConeIso (value s) (value t)
  action {s = s} {t} Φ = record
    { leftIso = ConeIso.leftIso Φ ; rightIso = ConeIso.rightIso Φ
    ; compatible = isoComp-assoc-at (a′ ◁ ConeIso.rightIso Φ) (θ ▷ Cone.right s) (Cone.match s) ∙
      (isoComp-cong (interchange-at θ (ConeIso.rightIso Φ)) (idIso (Cone.match s)) ∙
      ((isoComp-assoc-at (θ ▷ Cone.right t) (a ◁ ConeIso.rightIso Φ) (Cone.match s)) ⁻¹ ∙
      (isoComp-cong (idIso (θ ▷ Cone.right t)) (ConeIso.compatible Φ) ∙
        isoComp-assoc-at (θ ▷ Cone.right t) (Cone.match t) (u ◁ ConeIso.leftIso Φ)))) }

  restrict : {Γ Δ : CAT} (h : MAP Δ Γ) (s : Cone u a Γ) →
    ConeIso (conePre h (value s)) (value (conePre h s))
  restrict h s = cone-match-change _ _ _ _
    (isoComp-assoc-at (θ ▷ (Cone.right s ∘ h)) (comp-assoc h (Cone.right s) a)
      ((Cone.match s ▷ h) ∙ (comp-assoc h (Cone.left s) u) ⁻¹) ∙
    (isoComp-cong (preWhisker-comp-at θ (Cone.right s) h)
      (idIso ((Cone.match s ▷ h) ∙ (comp-assoc h (Cone.left s) u) ⁻¹)) ∙
    ((isoComp-assoc-at (comp-assoc h (Cone.right s) a′) ((θ ▷ Cone.right s) ▷ h)
      ((Cone.match s ▷ h) ∙ (comp-assoc h (Cone.left s) u) ⁻¹)) ⁻¹ ∙
    (isoComp-cong (idIso (comp-assoc h (Cone.right s) a′))
      (isoComp-assoc-at ((θ ▷ Cone.right s) ▷ h) (Cone.match s ▷ h)
        ((comp-assoc h (Cone.left s) u) ⁻¹)) ∙
      isoComp-cong (idIso (comp-assoc h (Cone.right s) a′))
        (isoComp-cong (preWhisker-isoComp-at (θ ▷ Cone.right s) (Cone.match s) h)
          (idIso ((comp-assoc h (Cone.left s) u) ⁻¹)))))))
```

Changing the specified identification by a higher comparison changes the
selected fiber functor by a lifted comparison. Its full image is prescribed
by the given higher comparison of matchings.

```agda
module Congruence {C D B : CAT} (u : MAP C D) {a a′ : MAP B D}
  (θ θ′ : a =₁ a′) (χ : θ =₂ θ′) where
  private
    module Before = Change u θ using (map; value; computation)
    module After = Change u θ′ using (map; value; computation)
    source = pullbackCone u a
    target = pullbackCone u a′
  value-comparison : {Γ : CAT} (s : Cone u a Γ) → ConeIso (Before.value s) (After.value s)
  value-comparison s = cone-match-change _ _ _ _
    (isoComp-cong (preWhisker (Cone.right s) ◁ χ) (idIso (Cone.match s)))

  prescribed : ConeIso (conePre Before.map target) (conePre After.map target)
  prescribed = coneIso-compose (coneIso-inverse After.computation)
    (coneIso-compose (value-comparison source) Before.computation)
  private
    module Lifted = Lifting.Lift 𝒯 P Before.map After.map prescribed
      using (lift; comparison-image; left-image; right-image)
  open Lifted public using (comparison-image; left-image; right-image) renaming (lift to comparison)
```
