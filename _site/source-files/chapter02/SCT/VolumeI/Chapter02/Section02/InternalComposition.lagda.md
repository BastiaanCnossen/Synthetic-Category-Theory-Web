# Internal composition between functor categories

Curry the evaluation of a pair of composable functors. Named values and both
fixed-input functors retain their uncurried comparison images. This ports the
old argument into the ambient foundation without its file parameter tower.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.InternalComposition where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; comp-unitˡ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair; pair⁼; pair-pre; pair-β₁; pair-β₂)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funCurry; funCurry-β; funUncurry; reflect; reflect-β-One)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-restrict; evaluate-cong; evaluate-id)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPost; funPre-β; funPost-β)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
import SCT.VolumeI.Chapter01.Section09.NamedEvaluation as NamedEvaluationOwner

private
  uncurry-restrict : {Γ : Context} {P Q C D : CAT Γ} (f : MAP P (Fun C D)) (r : MAP Q P)
    → funUncurry (f ∘ r) =₁ (funUncurry f ∘ productMap r (id C))
  uncurry-restrict {C = C} {D} f r = evaluate-restrict (funEval {C = C} {D = D}) f r

product-pair : {Γ : Context} {P A B C D : CAT Γ} (f : MAP A C) (g : MAP B D) (h : MAP P A) (k : MAP P B) →
  (productMap f g ∘ pair h k) =₁ pair (f ∘ h) (g ∘ k)
product-pair f g h k = productMap-pair f g h k

named-application : {Γ : Context} {P C D : CAT Γ} (f : MAP C D) (r : MAP P One) (h : MAP P C) →
  (funEval ∘ pair (funName f ∘ r) h) =₁ (f ∘ h)
named-application f r h = (f ◁ pair-β₂ r h) ∙
  comp-assoc (pair r h) pr₂ f ∙ (funCurry-β (f ∘ pr₂) ▷ pair r h) ∙
  (comp-assoc (pair r h) (productMap (funName f) (id _)) funEval) ⁻¹ ∙
  (funEval ◁ (pair⁼ (id₌ (funName f ∘ r)) (comp-unitˡ h) ∙
    product-pair (funName f) (id _) r h) ⁻¹)

named-uncurry : {Γ : Context} {P C D : CAT Γ} (f : MAP C D) (r : MAP P One) →
  funUncurry (funName f ∘ r) =₁ (f ∘ pr₂)
named-uncurry {C = C} {D = D} f r =
  NamedEvaluationOwner.NamedEvaluation.named-evaluation {C = C} {S = D} f r

module At {Γ : Context} (B C D : CAT Γ) where
  X = Fun C D
  Y = Fun B C
  parameter = X × Y
  inner : MAP (parameter × B) C
  inner = funEval ∘ pair (pr₂ ∘ pr₁) pr₂
  input : MAP (parameter × B) (X × C)
  input = pair (pr₁ ∘ pr₁) inner
  diagram : MAP (parameter × B) D
  diagram = funEval ∘ input
  composeFunctor : MAP parameter (Fun B D)
  composeFunctor = funCurry diagram

  module Apply {P : CAT Γ} (F : MAP P X) (u : MAP P Y) where
    step : MAP (P × B) (parameter × B)
    step = productMap (pair F u) (id B)
    first : ((pr₁ ∘ pr₁) ∘ step) =₁ (F ∘ pr₁)
    first = (pair-β₁ F u ▷ pr₁) ∙ (comp-assoc pr₁ (pair F u) pr₁) ⁻¹ ∙
      (pr₁ ◁ pair-β₁ (pair F u ∘ pr₁) (id B ∘ pr₂)) ∙ comp-assoc step pr₁ pr₁
    second : ((pr₂ ∘ pr₁) ∘ step) =₁ (u ∘ pr₁)
    second = (pair-β₂ F u ▷ pr₁) ∙ (comp-assoc pr₁ (pair F u) pr₂) ⁻¹ ∙
      (pr₂ ◁ pair-β₁ (pair F u ∘ pr₁) (id B ∘ pr₂)) ∙ comp-assoc step pr₁ pr₂
    inner-comparison : (inner ∘ step) =₁ funUncurry u
    inner-comparison = (funEval ◁
      (pair⁼ second (pair-β₂ (pair F u ∘ pr₁) (id B ∘ pr₂)) ∙
        pair-pre (pr₂ ∘ pr₁) pr₂ step)) ∙ comp-assoc step (pair (pr₂ ∘ pr₁) pr₂) funEval
    input-comparison : (input ∘ step) =₁ pair (F ∘ pr₁) (funUncurry u)
    input-comparison = pair⁼ first inner-comparison ∙ pair-pre (pr₁ ∘ pr₁) inner step
    comparison : funUncurry (composeFunctor ∘ pair F u) =₁
      (funEval ∘ pair (F ∘ pr₁) (funUncurry u))
    comparison = (funEval ◁ input-comparison) ∙ comp-assoc step input funEval ∙
      (funCurry-β diagram ▷ step) ∙ uncurry-restrict composeFunctor (pair F u)

  module Named (F : MAP C D) (u : MAP B C) where
    raw : funUncurry (composeFunctor ∘ pair (funName F) (funName u)) =₁ funUncurry (funName (F ∘ u))
    raw = (funCurry-β ((F ∘ u) ∘ pr₂)) ⁻¹ ∙ (comp-assoc pr₂ u F) ⁻¹ ∙
      named-application F pr₁ (u ∘ pr₂) ∙
      (funEval ◁ pair⁼ (id₌ (funName F ∘ pr₁)) (funCurry-β (u ∘ pr₂))) ∙
      Apply.comparison (funName F) (funName u)
    comparison : (composeFunctor ∘ pair (funName F) (funName u)) =₁ funName (F ∘ u)
    comparison = reflect (funEval {C = B} {D = D}) (funUniversal B D) _ _ raw
    image : evaluate-cong (funEval {C = B} {D = D}) comparison =₂ raw
    image = reflect-β-One (funEval {C = B} {D = D}) (funUniversal B D) _ _ raw

  module FixRight (u : MAP B C) where
    insertion : MAP X parameter
    insertion = pair (id X) (const (funName u))
    raw : funUncurry (composeFunctor ∘ insertion) =₁ funUncurry (funPre {D = D} u)
    raw = (funPre-β u) ⁻¹ ∙
      (funEval ◁ pair⁼ (id₌ (id X ∘ pr₁)) (named-uncurry u (terminate X))) ∙
      Apply.comparison (id X) (const (funName u))
    comparison : (composeFunctor ∘ insertion) =₁ funPre u
    comparison = reflect (funEval {C = B} {D = D}) (funUniversal B D) _ _ raw
    image : evaluate-cong (funEval {C = B} {D = D}) comparison =₂ raw
    image = reflect-β-One (funEval {C = B} {D = D}) (funUniversal B D) _ _ raw

  module FixLeft (F : MAP C D) where
    insertion : MAP Y parameter
    insertion = pair (const (funName F)) (id Y)
    raw : funUncurry (composeFunctor ∘ insertion) =₁ funUncurry (funPost {C = B} F)
    raw = (funPost-β F) ⁻¹ ∙ named-application F (terminate Y ∘ pr₁) funEval ∙
      (funEval ◁ pair⁼ (comp-assoc pr₁ (terminate Y) (funName F)) (evaluate-id (funEval {C = B} {D = C}))) ∙
      Apply.comparison (const (funName F)) (id Y)
    comparison : (composeFunctor ∘ insertion) =₁ funPost F
    comparison = reflect (funEval {C = B} {D = D}) (funUniversal B D) _ _ raw
    image : evaluate-cong (funEval {C = B} {D = D}) comparison =₂ raw
    image = reflect-β-One (funEval {C = B} {D = D}) (funUniversal B D) _ _ raw
```
