# Reading framed arrows from source-endpoint cones

A cone on source evaluation and an object determines a framed arrow.
Its parameter map to the terminal category is normalized using the
specified terminal comparison. Comparisons of cones retain the source
frame and induce the corresponding comparison of target objects.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.SourceConeExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone; ConeIso)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneIso-adjust)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (same-arrow)
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as CosliceRead
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (conePre)
import SCT.VolumeI.Chapter01.Section03.Equivalences as Terminal
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
open Terminal.TerminalTargets vocabulary terminal products productLaws composition using (terminal-Iso₂)

module At {Γ C : CAT} (x : Obj-abs C) (s : Cone (ev₀ {C}) x Γ) where
  parameter-frame : Cone.right s =₁ terminate Γ
  parameter-frame = terminal-iso (Cone.right s) (terminate Γ)

  decoded : MorphismExpression (const x) (ev₁ ∘ Cone.left s)
  decoded = record { arrow = Cone.left s
    ; source-frame = (x ◁ parameter-frame) ∙ Cone.match s
    ; target-frame = idIso (ev₁ ∘ Cone.left s) }

  normalized : Cone ev₀ x Γ
  normalized = record { left = Cone.left s ; right = terminate Γ
    ; match = MorphismExpression.source-frame decoded }

  abstract
    computation : ConeIso s normalized
    computation = record { leftIso = idIso (Cone.left s) ; rightIso = parameter-frame
      ; compatible = isoComp-unitʳ-at (Cone.match normalized) ∙
          isoComp-cong (idIso (Cone.match normalized)) (postWhisker-idIso ev₀ (Cone.left s)) }

module Compared {Γ C : CAT} (x : Obj-abs C) {s t : Cone (ev₀ {C}) x Γ}
  (Φ : ConeIso s t) where
  private
    module Before = At x s using (decoded; parameter-frame)
    module After = At x t using (decoded; parameter-frame)
    α = ConeIso.leftIso Φ
    β = ConeIso.rightIso Φ
    a₀ = x ◁ After.parameter-frame
    b₀ = x ◁ β
    τ = Cone.match t
    σ = Cone.match s
    left-image : (ev₀ ∘ Cone.left s) =₁ (ev₀ ∘ Cone.left t)
    left-image = ev₀ ◁ α

    abstract
      parameter-composition : (a₀ ∙ b₀) =₂ (x ◁ Before.parameter-frame)
      parameter-composition = (postWhisker x ◁ terminal-Iso₂
        (After.parameter-frame ∙ β) Before.parameter-frame) ∙
        (postWhisker-isoComp-at x After.parameter-frame β) ⁻¹

      source-matching : ((a₀ ∙ τ) ∙ left-image) =₂
        (idIso (const x) ∙ ((x ◁ Before.parameter-frame) ∙ σ))
      source-matching = (isoComp-unitˡ-at ((x ◁ Before.parameter-frame) ∙ σ)) ⁻¹ ∙
        (isoComp-cong parameter-composition (idIso σ) ∙
        ((isoComp-assoc-at a₀ b₀ σ) ⁻¹ ∙
        (isoComp-cong (idIso a₀) (ConeIso.compatible Φ) ∙
          (isoComp-assoc-at a₀ τ left-image))))

  abstract
    comparison : ExpressionIso
      (retarget-expression Before.decoded (idIso (const x)) (ev₁ ◁ α)) After.decoded
    comparison = record { comparison = α ; source-compatible = source-matching
      ; target-compatible = (isoComp-unitʳ-at (ev₁ ◁ α)) ⁻¹ ∙ isoComp-unitˡ-at (ev₁ ◁ α) }

module Read {Γ C : CAT} (x : Obj-abs C) (h : MAP Γ (Coslice C x)) where
  private
    module H = EndpointFiber (const x) (id C)
    module Reading = CosliceRead.At 𝒯 M ℱ P I x using (read)
    source-square = CosliceEndpoint.square x
    restricted-square = conePre h source-square
    module Decoded = At x restricted-square using (decoded; parameter-frame)
    X₀ = x ◁ Decoded.parameter-frame
    A₀ = comp-assoc h (terminate (Coslice C x)) x
    B₀ = (Cone.match source-square ▷ h) ∙ (comp-assoc h H.arrow ev₀) ⁻¹
    target-frame = MorphismExpression.target-frame (Reading.read h)

  abstract
    comparison : ExpressionIso
      (retarget-expression Decoded.decoded (idIso (const x)) target-frame)
      (Reading.read h)
    comparison = same-arrow (H.arrow ∘ h) _ _ _ _
      ((isoComp-unitˡ-at (X₀ ∙ (A₀ ∙ B₀))) ⁻¹ ∙ isoComp-assoc-at X₀ A₀ B₀)
      ((isoComp-unitʳ-at target-frame) ⁻¹)

module FromCone {Γ C : CAT} (x : Obj-abs C) (h : MAP Γ (Coslice C x))
  {y : MAP Γ C} (v : MorphismExpression (const x) y)
  (Φ : ConeIso (conePre h (CosliceEndpoint.square x))
    (record { left = MorphismExpression.arrow v ; right = terminate Γ
      ; match = MorphismExpression.source-frame v })) where
  private
    module Reading = CosliceRead.At 𝒯 M ℱ P I x using (read)
    module H = EndpointFiber (const x) (id C)
    a₀ = ConeIso.leftIso Φ
    b₀ = ConeIso.rightIso Φ
    η = terminal-iso (terminate (Coslice C x) ∘ h) (terminate Γ)
    X₀ = x ◁ η
    A₀ = comp-assoc h (terminate (Coslice C x)) x
    B₀ = (Cone.match (CosliceEndpoint.square x) ▷ h) ∙ (comp-assoc h H.arrow ev₀) ⁻¹
    r₀ = MorphismExpression.target-frame (Reading.read h)
    t₀ = MorphismExpression.target-frame v
    l₀ = ev₁ ◁ a₀

  target-comparison : (coslice-projection x ∘ h) =₁ y
  target-comparison = (t₀ ∙ l₀) ∙ r₀ ⁻¹

  abstract
    comparison : ExpressionIso
      (retarget-expression (Reading.read h) (idIso (const x)) target-comparison) v
    comparison = record { comparison = a₀
      ; source-compatible = (isoComp-unitˡ-at (MorphismExpression.source-frame (Reading.read h))) ⁻¹ ∙
          ((isoComp-assoc-at X₀ A₀ B₀) ⁻¹ ∙
          (isoComp-cong (postWhisker x ◁ terminal-Iso₂ b₀ η) (idIso (A₀ ∙ B₀)) ∙
            ConeIso.compatible Φ))
      ; target-compatible = (cancel-inverse-tail (t₀ ∙ l₀) r₀) ⁻¹ }
```



