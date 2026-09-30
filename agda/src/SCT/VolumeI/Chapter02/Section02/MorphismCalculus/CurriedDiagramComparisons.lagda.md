# Reflecting comparisons of curried interval diagrams

An identification of uncurried diagrams lifts through the exponential
universal property. Its endpoint equations lift as well, provided the
uncurried equations retain the parameter-restriction comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurriedDiagramComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β; funReflect-Iso₂)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications as Diagrams
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

module Reflect {Γ X C : CAT} (H K : MAP (Γ × [1]) (Fun X C))
  (δ : funUncurry H =₁ funUncurry K) where
  comparison = funIsoReflect H K δ

  endpoint-image : (z : Obj-abs [1]) {h : MAP Γ (Fun X C)} →
    (H ∘ insert z) =₁ h → (funUncurry H ∘ productMap (insert z) (id X)) =₁ funUncurry h
  endpoint-image z p = funUncurryIso p ∙ (funUncurry-restrict H (insert z)) ⁻¹

  module Endpoint (z : Obj-abs [1]) (h : MAP Γ (Fun X C))
    (p : (H ∘ insert z) =₁ h) (q : (K ∘ insert z) =₁ h)
    (square : ((funUncurryIso q ∙ (funUncurry-restrict K (insert z)) ⁻¹) ∙
      (δ ▷ productMap (insert z) (id X))) =₂ endpoint-image z p) where
    i = insert {X = Γ} z
    step = productMap i (id X)
    h-step = funUncurry-restrict H i
    k-step = funUncurry-restrict K i
    d = funUncurryIso (comparison ▷ i)
    e = δ ▷ step
    r = funUncurryIso q

    abstract
      restriction-square : (k-step ∙ d) =₂ (e ∙ h-step)
      restriction-square =
        isoComp-cong (preWhisker step ◁ funIsoReflect-β H K δ) (idIso h-step) ∙
        funUncurry-restrict-inputs comparison i

      compatible : (q ∙ (comparison ▷ i)) =₂ p
      compatible = funReflect-Iso₂ _ _
        (cancel-right-reflect (h-step ⁻¹)
          (square ∙ (isoComp-assoc-at r (k-step ⁻¹) e) ⁻¹ ∙
            isoComp-cong (idIso r) ((move-square k-step d e h-step restriction-square) ⁻¹) ∙
            isoComp-assoc-at r d (h-step ⁻¹)) ∙
          funUncurryIso-comp q (comparison ▷ i))

  module WithEndpoints {f g : MAP Γ (Fun X C)}
    (p : (H ∘ insert zero) =₁ f) (q : (H ∘ insert one) =₁ g)
    (p′ : (K ∘ insert zero) =₁ f) (q′ : (K ∘ insert one) =₁ g)
    (source : ((funUncurryIso p′ ∙ (funUncurry-restrict K (insert zero)) ⁻¹) ∙
      (δ ▷ productMap (insert zero) (id X))) =₂ endpoint-image zero p)
    (target : ((funUncurryIso q′ ∙ (funUncurry-restrict K (insert one)) ⁻¹) ∙
      (δ ▷ productMap (insert one) (id X))) =₂ endpoint-image one q) where
    value : ExpressionIso (expression H p q) (expression K p′ q′)
    value = Diagrams.At.comparison 𝒯 M ℱ P I E H K comparison p q p′ q′
      (Endpoint.compatible zero f p p′ source) (Endpoint.compatible one g q q′ target)
```
