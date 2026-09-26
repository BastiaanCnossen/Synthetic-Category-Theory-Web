# Evaluating the product associativity comparison

Postcomposition with an evaluation functor transports the product
composition law. The comparison retains the associators used when an
evaluation is performed in two successive steps.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductCompositionAssociativity as Products

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductEvaluationAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.Substitution.IteratedCompatibility 𝒯 M
  using (evaluation-step; evaluation-step-iterated)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pre-inverse-at; solve-pentagon)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (move-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at)

module Evaluation {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ E : CAT}
  (f₀ : MAP A₀ A₁) (f₁ : MAP A₁ A₂) (f₂ : MAP A₂ A₃)
  (g₀ : MAP B₀ B₁) (g₁ : MAP B₁ B₂) (g₂ : MAP B₂ B₃)
  (e : MAP (A₃ × B₃) E) where

  module Product = Products.ProductCompositor 𝒯 M f₀ f₁ f₂ g₀ g₁ g₂
  t = productMap f₀ g₀
  s = productMap f₁ g₁
  p = productMap f₂ g₂
  st = productMap (f₁ ∘ f₀) (g₁ ∘ g₀)
  ps = productMap (f₂ ∘ f₁) (g₂ ∘ g₁)
  leftTriple = productMap ((f₂ ∘ f₁) ∘ f₀) ((g₂ ∘ g₁) ∘ g₀)
  rightTriple = productMap (f₂ ∘ (f₁ ∘ f₀)) (g₂ ∘ (g₁ ∘ g₀))
  κ01 = productMap-comp f₀ f₁ g₀ g₁
  κ12 = productMap-comp f₁ f₂ g₁ g₂
  κ012-left = productMap-comp f₀ (f₂ ∘ f₁) g₀ (g₂ ∘ g₁)
  κ012-right = productMap-comp (f₁ ∘ f₀) f₂ (g₁ ∘ g₀) g₂
  associator : leftTriple =₁ rightTriple
  associator = productMap-cong (comp-assoc f₀ f₁ f₂) (comp-assoc g₀ g₁ g₂)
  firstStep = evaluation-step e p s (κ12 ⁻¹)
  secondStep = evaluation-step e ps t (κ012-left ⁻¹)
  combinedStep = evaluation-step e p st (κ012-right ⁻¹)
  together = combinedStep ∙ (e ◁ associator)
  successively = ((e ∘ p) ◁ κ01) ∙
    (comp-assoc t s (e ∘ p) ∙ ((firstStep ▷ t) ∙ secondStep))

  abstract
    law : together =₂ successively
    law =
      (let a = κ12 ⁻¹
           b = κ012-left ⁻¹
           inner = comp-assoc t s p ∙ ((a ▷ t) ∙ b)
           outside = (comp-assoc st p e) ⁻¹
           middle = (comp-assoc (s ∘ t) p e) ⁻¹
           whiskered-κ = p ◁ κ01
           commute = (move-square (comp-assoc st p e)
             ((e ∘ p) ◁ κ01) (e ◁ whiskered-κ) (comp-assoc (s ∘ t) p e)
             (postWhisker-comp-at κ01 p e)) ⁻¹
           solve = solve-pentagon κ012-right
             (whiskered-κ ∙ comp-assoc t s p) associator κ012-left (κ12 ▷ t) Product.law ∙
             ((isoComp-assoc-at whiskered-κ (comp-assoc t s p) ((κ12 ▷ t) ⁻¹ ∙ b)) ⁻¹ ∙
              isoComp-cong (idIso whiskered-κ)
                (isoComp-cong (idIso (comp-assoc t s p))
                  (isoComp-cong (pre-inverse-at κ12 t) (idIso b))))
       in (isoComp-assoc-at outside (e ◁ κ012-right ⁻¹) (e ◁ associator)) ⁻¹ ∙
         (isoComp-cong (idIso outside) (postWhisker-isoComp-at e (κ012-right ⁻¹) associator) ∙
         (isoComp-cong (idIso outside) (postWhisker e ◁ solve) ∙
         (isoComp-cong (idIso outside) ((postWhisker-isoComp-at e whiskered-κ inner) ⁻¹) ∙
         (isoComp-assoc-at outside (e ◁ whiskered-κ) (e ◁ inner) ∙
         (isoComp-cong commute (idIso (e ◁ inner)) ∙
         ((isoComp-assoc-at ((e ∘ p) ◁ κ01) middle (e ◁ inner)) ⁻¹ ∙
           isoComp-cong (idIso ((e ∘ p) ◁ κ01))
             (evaluation-step-iterated e p s t a b)))))))) ⁻¹
```
