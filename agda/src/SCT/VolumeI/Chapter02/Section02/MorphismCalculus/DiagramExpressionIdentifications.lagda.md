# Identifications of diagrams with specified endpoints

Currying a diagram identification preserves the two chosen endpoint
identifications. The reflected comparison retains its uncurried image.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ using (funIsoReflect; funIsoReflect-β)
open import SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitTriangles 𝒯 M ℱ P I E using (module ReflectedEndpoint)

module At {Γ C : CAT} {x y : MAP Γ C}
  (H K : MAP (Γ × [1]) C) (δ : H =₁ K)
  (p : (H ∘ insert zero) =₁ x) (q : (H ∘ insert one) =₁ y)
  (p′ : (K ∘ insert zero) =₁ x) (q′ : (K ∘ insert one) =₁ y)
  (source : (p′ ∙ (δ ▷ insert zero)) =₂ p)
  (target : (q′ ∙ (δ ▷ insert one)) =₂ q) where
  h = funCurry H
  k = funCurry K
  β = funCurry-β K
  θ = δ ∙ funCurry-β H
  comparison-arrow = funIsoReflect h k (β ⁻¹ ∙ θ)

  module Endpoint (v : Obj-abs [1]) {z : MAP Γ C}
    (r : (H ∘ insert v) =₁ z) (r′ : (K ∘ insert v) =₁ z)
    (same : (r′ ∙ (δ ▷ insert v)) =₂ r) where
    i = insert {X = Γ} v
    Q = evaluate-uncurry v h
    b = funCurry-β H ▷ i
    d = δ ▷ i
    module Reflected = ReflectedEndpoint v h k β θ comparison-arrow
      (funIsoReflect-β h k (β ⁻¹ ∙ θ))

    abstract
      compatible : ((r′ ∙ evaluate-curry v K) ∙ (evaluate v ◁ comparison-arrow)) =₂
        (r ∙ evaluate-curry v H)
      compatible = isoComp-cong same (idIso (b ∙ Q)) ∙
        (isoComp-assoc-at r′ d (b ∙ Q)) ⁻¹ ∙
        isoComp-cong (idIso r′) (isoComp-assoc-at d b Q ∙
          isoComp-cong (preWhisker-isoComp-at δ (funCurry-β H) i) (idIso Q)) ∙
        isoComp-cong (idIso r′) Reflected.endpoint ∙
        isoComp-assoc-at r′ (evaluate-curry v K) (evaluate v ◁ comparison-arrow)

  comparison : ExpressionIso (expression H p q) (expression K p′ q′)
  comparison = record { comparison = comparison-arrow
    ; source-compatible = Endpoint.compatible zero p p′ source
    ; target-compatible = Endpoint.compatible one q q′ target }
```

Every expression is identified with the curried form of its uncurried
diagram. The endpoint comparisons are part of this recovery.

```agda
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointNaturality 𝒯 M ℱ using (module Evaluation)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)

module Recovery {Γ C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) where
  module F = MorphismExpression f
  h = F.arrow
  H = funUncurry h
  p = F.source-frame ∙ (evaluate-uncurry zero h) ⁻¹
  q = F.target-frame ∙ (evaluate-uncurry one h) ⁻¹
  result = expression H p q
  β = funCurry-β H
  comparison-arrow = funIsoReflect h (funCurry H) (β ⁻¹ ∙ idIso H)
  module Endpoint (v : Obj-abs [1]) {z : MAP Γ C}
    (r : (evaluate v ∘ h) =₁ z) where
    i = insert {X = Γ} v
    Q = evaluate-uncurry v h
    front = r ∙ Q ⁻¹
    module Reflected = ReflectedEndpoint v h (funCurry H) β (idIso H) comparison-arrow
      (funIsoReflect-β h (funCurry H) (β ⁻¹ ∙ idIso H))
    abstract
      compatible : ((front ∙ evaluate-curry v H) ∙ (evaluate v ◁ comparison-arrow)) =₂ r
      compatible = cancel-inverse-tail r Q ∙
        isoComp-cong (idIso front)
          (isoComp-unitˡ-at Q ∙ isoComp-cong (preWhisker-idIso H i) (idIso Q)) ∙
        isoComp-cong (idIso front) Reflected.endpoint ∙
        isoComp-assoc-at front (evaluate-curry v H) (evaluate v ◁ comparison-arrow)

  comparison : ExpressionIso f result
  comparison = record { comparison = comparison-arrow
    ; source-compatible = Endpoint.compatible zero F.source-frame
    ; target-compatible = Endpoint.compatible one F.target-frame }
```

```agda
retarget-curried : {Γ C : CAT} {x y x′ y′ : MAP Γ C}
  (H : MAP (Γ × [1]) C) (p : (H ∘ insert zero) =₁ x) (q : (H ∘ insert one) =₁ y)
  (α : x =₁ x′) (β : y =₁ y′) →
  ExpressionIso (retarget-expression (expression H p q) α β)
    (expression H (α ∙ p) (β ∙ q))
retarget-curried H p q α β = record
  { comparison = idIso (funCurry H)
  ; source-compatible = isoComp-assoc-at α p (evaluate-curry zero H) ∙
      isoComp-unitʳ-at ((α ∙ p) ∙ evaluate-curry zero H) ∙
      isoComp-cong (idIso ((α ∙ p) ∙ evaluate-curry zero H)) (postWhisker-idIso ev₀ (funCurry H))
  ; target-compatible = isoComp-assoc-at β q (evaluate-curry one H) ∙
      isoComp-unitʳ-at ((β ∙ q) ∙ evaluate-curry one H) ∙
      isoComp-cong (idIso ((β ∙ q) ∙ evaluate-curry one H)) (postWhisker-idIso ev₁ (funCurry H)) }
```
