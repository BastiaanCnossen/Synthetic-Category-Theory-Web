# Identifications after changing the target structure

Changing a target's structure functor transports native identifications
and reflects them. Interchange retains the specified base triangle.
Applying the inverse change cancels, so no embedding assumption is needed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.Section05.Currying.TargetChangeIdentifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P using (triangle-identification)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P using (change-target-back)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right; move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (preWhisker-comp-at)

module Change {C D S : CAT} {f : MAP C S} {g g′ : MAP D S} (γ : g′ =₁ g) where
  abstract
    identification : {u v : FunctorOver f g} → FunctorOverIso u v →
      FunctorOverIso (change-target-back γ u) (change-target-back γ v)
    identification {u} {v} Φ = record { underlying = FunctorOverIso.underlying Φ
      ; compatible = isoComp-cong (FunctorOverIso.compatible Φ) (idIso (γ ▷ FunctorLift.lift u)) ∙
          ((isoComp-assoc-at (FunctorLift.comparison v) (g ◁ FunctorOverIso.underlying Φ) (γ ▷ FunctorLift.lift u)) ⁻¹ ∙
            (isoComp-cong (idIso (FunctorLift.comparison v)) (interchange-at γ (FunctorOverIso.underlying Φ)) ∙
              isoComp-assoc-at (FunctorLift.comparison v) (γ ▷ FunctorLift.lift v) (g′ ◁ FunctorOverIso.underlying Φ))) }

    inverse-change : (u : FunctorOver f g) →
      FunctorOverIso (change-target-back (γ ⁻¹) (change-target-back γ u)) u
    inverse-change u = triangle-identification _ _ _
      (cancel-right (γ ▷ FunctorLift.lift u) (FunctorLift.comparison u) ∙
        isoComp-cong (idIso (FunctorLift.comparison u ∙ (γ ▷ FunctorLift.lift u))) (pre-inverse γ (FunctorLift.lift u)))

abstract
  reflect-target-change : {C D S : CAT} {f : MAP C S} {g g′ : MAP D S}
    (γ : g′ =₁ g) {u v : FunctorOver f g} →
    FunctorOverIso (change-target-back γ u) (change-target-back γ v) → FunctorOverIso u v
  reflect-target-change γ {u} {v} Φ = compose-iso-over (Change.inverse-change γ v)
    (compose-iso-over (Change.identification (γ ⁻¹) Φ) (inverse-iso-over (Change.inverse-change γ u)))

module Composite {A C D S : CAT} {f : MAP A S} {k : MAP C S} {g g′ : MAP D S}
  (γ : g′ =₁ g) (u : FunctorOver f k) (v : FunctorOver k g) where
  h = FunctorLift.lift u
  j = FunctorLift.lift v
  θ = FunctorLift.comparison u
  ψ = FunctorLift.comparison v ▷ h
  assoc = comp-assoc h j g
  assoc′ = comp-assoc h j g′
  δ = (γ ▷ j) ▷ h
  Γ = γ ▷ (j ∘ h)
  abstract
    comparison : FunctorOverIso (change-target-back γ (compose-over v u))
      (compose-over (change-target-back γ v) u)
    comparison = triangle-identification _ _ _
      (isoComp-cong (idIso θ)
        (isoComp-cong ((preWhisker-isoComp-at (FunctorLift.comparison v) (γ ▷ j) h) ⁻¹) (idIso (assoc′ ⁻¹))) ∙
        (isoComp-cong (idIso θ) ((isoComp-assoc-at ψ δ (assoc′ ⁻¹)) ⁻¹) ∙
          (isoComp-cong (idIso θ)
            (isoComp-cong (idIso ψ) (move-square assoc δ Γ assoc′ (preWhisker-comp-at γ j h))) ∙
            (isoComp-cong (idIso θ) (isoComp-assoc-at ψ (assoc ⁻¹) Γ) ∙
              isoComp-assoc-at θ (ψ ∙ assoc ⁻¹) Γ))))
```
