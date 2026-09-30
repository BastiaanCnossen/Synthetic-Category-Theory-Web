# Hom functors and their endpoint coordinates

An identification in a hom category retains both endpoint equations.
Conversely, an endpoint-preserving identification of expressions gives
an identification between the corresponding hom functors.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomCalculus.HomCoordinates
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
import SCT.VolumeI.Chapter01.Section03.Equivalences as TerminalComparisons
open TerminalComparisons.TerminalTargets vocabulary terminal products productLaws composition
  using (terminal-Iso₂)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PC
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open PC vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-substitution; substitution-square-projection)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at)

module EncodeComparison {Γ B C : CAT} (u v : MAP B C) (y : MAP Γ B)
  {f g : MorphismExpression (u ∘ y) (v ∘ y)} (Φ : ExpressionIso f g) where
  private
    module F = MorphismExpression f
    module G = MorphismExpression g
    δ = ExpressionIso.comparison Φ
    p = pair-cong F.source-frame F.target-frame
    q = pair-cong G.source-frame G.target-frame
    before = pair-pre ev₀ ev₁ F.arrow
    after = pair-pre ev₀ ev₁ G.arrow
    r = (pair-pre u v y) ⁻¹
    d = pair-cong (ev₀ ◁ δ) (ev₁ ◁ δ)
    e = endpoints ◁ δ

    paired : (q ∙ d) =₂ p
    paired = pair-cong-Iso₂ (ExpressionIso.source-compatible Φ) (ExpressionIso.target-compatible Φ) ∙
      (pair-cong-comp G.source-frame (ev₀ ◁ δ) G.target-frame (ev₁ ◁ δ)) ⁻¹

    matching : ((r ∙ (q ∙ after)) ∙ e) =₂ (r ∙ (p ∙ before))
    matching = isoComp-cong (idIso r) (isoComp-cong paired (idIso before)) ∙
      (isoComp-cong (idIso r) ((isoComp-assoc-at q d before) ⁻¹) ∙
        (isoComp-cong (idIso r) (isoComp-cong (idIso q)
          ((pair-pre-natural-substitution ev₀ ev₁ δ) ⁻¹)) ∙
          (isoComp-cong (idIso r) (isoComp-assoc-at q after e) ∙
            isoComp-assoc-at r (q ∙ after) e)))

  comparison : ConeIso (EndpointFiber.cone u v y f) (EndpointFiber.cone u v y g)
  comparison = record { leftIso = δ ; rightIso = idIso y
    ; compatible = (isoComp-unitˡ-at (r ∙ (p ∙ before)) ∙
        isoComp-cong (postWhisker-idIso (pair u v) y) (idIso (r ∙ (p ∙ before)))) ⁻¹ ∙ matching }

hom-cong : {Γ C : CAT} {x y : Obj-abs C}
  {f g : MorphismExpression (const {P = Γ} x) (const y)} →
  ExpressionIso f g → hom-intro f =₁ hom-intro g
hom-cong {Γ} {x = x} {y} Φ = pullbackLift-cong (EncodeComparison.comparison x y (terminate Γ) Φ)

module ConstantBase {Γ A C : CAT} (b : MAP A One) (x : Obj-abs C)
  {h k : MAP Γ A} (α : h =₁ k) where
  th = terminal-iso (b ∘ h) (terminate Γ)
  tk = terminal-iso (b ∘ k) (terminate Γ)
  at-h = (x ◁ th) ∙ comp-assoc h b x
  at-k = (x ◁ tk) ∙ comp-assoc k b x

  natural : (at-k ∙ ((x ∘ b) ◁ α)) =₂ at-h
  natural = isoComp-cong
    ((postWhisker x ◁ terminal-Iso₂ (tk ∙ (b ◁ α)) th) ∙
      (postWhisker-isoComp-at x tk (b ◁ α)) ⁻¹) (idIso (comp-assoc h b x)) ∙
    ((isoComp-assoc-at (x ◁ tk) (x ◁ (b ◁ α)) (comp-assoc h b x)) ⁻¹ ∙
      (isoComp-cong (idIso (x ◁ tk)) (postWhisker-comp-at α b x) ∙
        isoComp-assoc-at (x ◁ tk) (comp-assoc k b x) ((x ∘ b) ◁ α)))

module HomIdentification {Γ C : CAT} {x y : Obj-abs C}
  {h k : MAP Γ (Hom C x y)} (α : h =₁ k) where
  module H = EndpointFiber x y

  endpoint : (π : MAP (Ar C) C) (z : Obj-abs C) (frame : (π ∘ H.arrow) =₁ (z ∘ H.base)) →
    (((z ◁ terminal-iso (H.base ∘ k) (terminate Γ)) ∙
      (comp-assoc k H.base z ∙ ((frame ▷ k) ∙ (comp-assoc k H.arrow π) ⁻¹))) ∙
      (π ◁ (H.arrow ◁ α))) =₂
    ((z ◁ terminal-iso (H.base ∘ h) (terminate Γ)) ∙
      (comp-assoc h H.base z ∙ ((frame ▷ h) ∙ (comp-assoc h H.arrow π) ⁻¹)))
  endpoint π z frame = isoComp-assoc-at nh Ah bh ∙
    (isoComp-cong (ConstantBase.natural H.base z α) (idIso bh) ∙
      ((isoComp-assoc-at (nk ∙ Ak) ((z ∘ H.base) ◁ α) bh) ⁻¹ ∙
        (isoComp-cong (idIso (nk ∙ Ak)) (substitution-square-projection π H.arrow (z ∘ H.base) frame α) ∙
          (isoComp-assoc-at (nk ∙ Ak) bk (π ◁ (H.arrow ◁ α)) ∙
            isoComp-cong ((isoComp-assoc-at nk Ak bk) ⁻¹) (idIso (π ◁ (H.arrow ◁ α)))))))
    where
    nh = z ◁ terminal-iso (H.base ∘ h) (terminate Γ)
    nk = z ◁ terminal-iso (H.base ∘ k) (terminate Γ)
    Ah = comp-assoc h H.base z
    Ak = comp-assoc k H.base z
    bh = (frame ▷ h) ∙ (comp-assoc h H.arrow π) ⁻¹
    bk = (frame ▷ k) ∙ (comp-assoc k H.arrow π) ⁻¹

  comparison : ExpressionIso (hom-expression h) (hom-expression k)
  comparison = record { comparison = H.arrow ◁ α
    ; source-compatible = endpoint ev₀ x H.source-frame
    ; target-compatible = endpoint ev₁ y H.target-frame }

hom-expression-cong : {Γ C : CAT} {x y : Obj-abs C} {h k : MAP Γ (Hom C x y)} →
  h =₁ k → ExpressionIso (hom-expression h) (hom-expression k)
hom-expression-cong = HomIdentification.comparison
```
