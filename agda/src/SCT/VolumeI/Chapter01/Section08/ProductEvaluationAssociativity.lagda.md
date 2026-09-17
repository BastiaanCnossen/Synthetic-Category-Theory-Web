# Evaluating the product associativity comparison

Postcomposition with an evaluation functor transports the product
composition law. The comparison retains the associators used when an
evaluation is performed in two successive steps.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section08.ProductCompositionAssociativity as Products

module SCT.VolumeI.Chapter01.Section08.ProductEvaluationAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section03.IteratedCompatibility 𝒯 M
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
  associator : NatIso leftTriple rightTriple
  associator = productMap-cong (comp-assoc f₀ f₁ f₂) (comp-assoc g₀ g₁ g₂)
  firstStep = evaluation-step e p s (invIso κ12)
  secondStep = evaluation-step e ps t (invIso κ012-left)
  combinedStep = evaluation-step e p st (invIso κ012-right)
  together = combinedStep ∙ (e ◁ associator)
  successively = ((e ∘ p) ◁ κ01) ∙
    (comp-assoc t s (e ∘ p) ∙ ((firstStep ▷ t) ∙ secondStep))

  abstract
    law : Iso₂ together successively
    law = invIso
      (let a = invIso κ12
           b = invIso κ012-left
           inner = comp-assoc t s p ∙ ((a ▷ t) ∙ b)
           outside = invIso (comp-assoc st p e)
           middle = invIso (comp-assoc (s ∘ t) p e)
           whiskered-κ = p ◁ κ01
           commute = invIso (move-square (comp-assoc st p e)
             ((e ∘ p) ◁ κ01) (e ◁ whiskered-κ) (comp-assoc (s ∘ t) p e)
             (postWhisker-comp-at κ01 p e))
           solve = solve-pentagon κ012-right
             (whiskered-κ ∙ comp-assoc t s p) associator κ012-left (κ12 ▷ t) Product.law ∙
             (invIso (isoComp-assoc-at whiskered-κ (comp-assoc t s p) (invIso (κ12 ▷ t) ∙ b)) ∙
              isoComp-cong (idIso whiskered-κ)
                (isoComp-cong (idIso (comp-assoc t s p))
                  (isoComp-cong (pre-inverse-at κ12 t) (idIso b))))
       in invIso (isoComp-assoc-at outside (e ◁ invIso κ012-right) (e ◁ associator)) ∙
         (isoComp-cong (idIso outside) (postWhisker-isoComp-at e (invIso κ012-right) associator) ∙
         (isoComp-cong (idIso outside) (postWhisker e ◁ solve) ∙
         (isoComp-cong (idIso outside) (invIso (postWhisker-isoComp-at e whiskered-κ inner)) ∙
         (isoComp-assoc-at outside (e ◁ whiskered-κ) (e ◁ inner) ∙
         (isoComp-cong commute (idIso (e ◁ inner)) ∙
         (invIso (isoComp-assoc-at ((e ∘ p) ◁ κ01) middle (e ◁ inner)) ∙
           isoComp-cong (idIso ((e ∘ p) ◁ κ01))
             (evaluation-step-iterated e p s t a b))))))))
```
