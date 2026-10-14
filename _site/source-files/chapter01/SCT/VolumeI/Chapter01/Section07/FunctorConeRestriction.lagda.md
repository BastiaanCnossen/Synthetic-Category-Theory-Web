# Restricting a natively evaluated cone

The complete restriction comparison uses the actual postcomposition
substitution squares and native evaluation of the specified matching.
Endpoint transport assembles their square. The component comparisons are
the existing selected `evaluate-restrict` triangles.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.FunctorConeRestriction where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; inv₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (inverse-unique; preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation using (evaluate-restrict-inputs)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Functoriality
open import SCT.VolumeI.Chapter01.Section07.FunctorCones
open import SCT.VolumeI.Chapter01.Section07.PostEvaluationSubstitution

private
  module _ {Γ : Context} {F K D : CAT Γ} (e : MAP (F × K) D) where
    evaluate-composite : {T : CAT Γ} {f g h : MAP T F} (β : g =₁ h) (α : f =₁ g)
      → evaluate-cong e (β ∙ α) =₂ (evaluate-cong e β ∙ evaluate-cong e α)
    evaluate-composite β α = comp₌-cong (evaluate⁼-absolute e β) (evaluate⁼-absolute e α) ∙
      (evaluate⁼-composition e β α ∙ (evaluate⁼-absolute e (β ∙ α)) ⁻¹)

    module _ {X T : CAT Γ} where
      open Terms.Equalities X using (_＝_)
      evaluate-inverse-family : {f g : MAP T F} (α : f ＝ g)
        → evaluate⁼ e (α ⁻¹) =₁ (evaluate⁼ e α) ⁻¹
      evaluate-inverse-family {f} α = (inverse-unique (evaluate⁼ e α) (evaluate⁼ e (α ⁻¹))
        (evaluate⁼-identity e f ∙
          (evaluate⁼-cong e (comp₌-inverseˡ α) ∙ (evaluate⁼-composition e (α ⁻¹) α) ⁻¹))) ⁻¹

    evaluate-inverse : {T : CAT Γ} {f g : MAP T F} (α : f =₁ g)
      → evaluate-cong e (α ⁻¹) =₂ (evaluate-cong e α) ⁻¹
    evaluate-inverse α = (inv₌ ◁ evaluate⁼-absolute e α) ∙
      (evaluate-inverse-family α ∙ (evaluate⁼-absolute e (α ⁻¹)) ⁻¹)

    evaluate-endpoints : {T : CAT Γ} {x x′ y y′ : MAP T F}
      (p : x =₁ x′) (q : y =₁ y′) (α : x =₁ y)
      → evaluate-cong e (changeEndpoints p q α) =₂
          changeEndpoints (evaluate-cong e p) (evaluate-cong e q) (evaluate-cong e α)
    evaluate-endpoints p q α = comp₌-cong (id₌ (evaluate-cong e q))
      (comp₌-cong (id₌ (evaluate-cong e α)) (evaluate-inverse p) ∙ evaluate-composite α (p ⁻¹)) ∙
      evaluate-composite q (α ∙ p ⁻¹)

    evaluate-identification-restrict : {R T : CAT Γ} {f g : MAP T F} (α : f =₁ g) (r : MAP R T)
      → SquareCell₌ (evaluate-cong e (α ▷ r)) (evaluate-cong e α ▷ productMap r (id K))
          (evaluate-restrict e f r) (evaluate-restrict e g r)
    evaluate-identification-restrict α r = unconst-sides₌
      (replace-edges₌ (evaluate⁼-absolute e (α ▷ r))
        (preWhisker (productMap r (id K)) ◁ evaluate⁼-absolute e α) (evaluate-restrict-inputs e α r))

  module _ {Γ : Context} {R T D : CAT Γ} where
    pre-endpoints : {x x′ y y′ : MAP T D}
      (p : x =₁ x′) (q : y =₁ y′) (α : x =₁ y) (r : MAP R T)
      → (changeEndpoints p q α ▷ r) =₂ changeEndpoints (p ▷ r) (q ▷ r) (α ▷ r)
    pre-endpoints p q α r = comp₌-cong (id₌ (q ▷ r))
      (comp₌-cong (id₌ (α ▷ r)) (preWhisker-inverse p r) ∙ preWhisker-comp₌ α (p ⁻¹) r) ∙
      preWhisker-comp₌ q (α ∙ p ⁻¹) r

module FunctorConeRestriction {Γ : Context} (K : CAT Γ) {C D E T R : CAT Γ}
  (f : MAP C E) (g : MAP D E) (r : MAP R T)
  (s : Cone (funPost {C = K} f) (funPost {C = K} g) T) where
  open FunctorCones K f g
  private
    p = Cone.left s
    q = Cone.right s
    τ = Cone.match s
    F = funPost {C = K} f
    G = funPost {C = K} g
    eC = funEval {C = K} {D = C}
    eD = funEval {C = K} {D = D}
    eE = funEval {C = K} {D = E}
    change = productMap r (id K)
    af = comp-assoc r p F
    ag = comp-assoc r q G
    Ef = funPost-uncurry {C = K} {D = C} {E = E} f (p ∘ r) ∙ evaluate-cong eE af
    Eg = funPost-uncurry {C = K} {D = D} {E = E} g (q ∘ r) ∙ evaluate-cong eE ag
    Ef′ = comp-assoc change (evaluate eC p) f ∙ (funPost-uncurry {C = K} {D = C} {E = E} f p ▷ change)
    Eg′ = comp-assoc change (evaluate eD q) g ∙ (funPost-uncurry {C = K} {D = D} {E = E} g q ▷ change)
    bf = evaluate-restrict eE (F ∘ p) r
    bg = evaluate-restrict eE (G ∘ q) r

  source = uncurryCone (cone-restrict r s)
  target = cone-restrict change (uncurryCone s)
  left = evaluate-restrict eC p r
  right = evaluate-restrict eD q r

  private
    rawSource = changeEndpoints Ef Eg (evaluate-cong eE (τ ▷ r))
    rawTarget = changeEndpoints Ef′ Eg′ (evaluate-cong eE τ ▷ change)
    source-normal : Cone.match source =₂ rawSource
    source-normal = changeEndpoints-iterated (evaluate-cong eE af) (evaluate-cong eE ag)
      (funPost-uncurry {C = K} {D = C} {E = E} f (p ∘ r)) (funPost-uncurry {C = K} {D = D} {E = E} g (q ∘ r)) (evaluate-cong eE (τ ▷ r)) ∙
      changeEndpoints-cong (funPost-uncurry {C = K} {D = C} {E = E} f (p ∘ r)) (funPost-uncurry {C = K} {D = D} {E = E} g (q ∘ r))
        (evaluate-endpoints eE af ag (τ ▷ r))
    target-normal : Cone.match target =₂ rawTarget
    target-normal = changeEndpoints-iterated (funPost-uncurry {C = K} {D = C} {E = E} f p ▷ change) (funPost-uncurry {C = K} {D = D} {E = E} g q ▷ change)
      (comp-assoc change (evaluate eC p) f) (comp-assoc change (evaluate eD q) g)
      (evaluate-cong eE τ ▷ change) ∙
      changeEndpoints-cong (comp-assoc change (evaluate eC p) f) (comp-assoc change (evaluate eD q) g)
        (pre-endpoints (funPost-uncurry {C = K} {D = C} {E = E} f p) (funPost-uncurry {C = K} {D = D} {E = E} g q) (evaluate-cong eE τ) change)
    raw-square : SquareCell₌ (f ◁ left) (g ◁ right) rawSource rawTarget
    raw-square = transport-square Ef Ef′ Eg Eg′ (evaluate-cong eE (τ ▷ r)) (evaluate-cong eE τ ▷ change)
      bf bg (f ◁ left) (g ◁ right)
      ((funPost-uncurry-restrict {K = K} {C = C} {D = E} {T = T} {R = R} f p r) ⁻¹ ∙
        comp₌-assoc (comp-assoc change (evaluate eC p) f)
          (funPost-uncurry {C = K} {D = C} {E = E} f p ▷ change) bf)
      ((funPost-uncurry-restrict {K = K} {C = D} {D = E} {T = T} {R = R} g q r) ⁻¹ ∙
        comp₌-assoc (comp-assoc change (evaluate eD q) g)
          (funPost-uncurry {C = K} {D = D} {E = E} g q ▷ change) bg)
      (transpose-square₌ (evaluate-identification-restrict eE τ r))

  comparison : ConeIdentification₁ source target
  comparison = record
    { left = left; right = right
    ; compatible = replace-sides₌ (source-normal ⁻¹) (target-normal ⁻¹) raw-square }

module _ {Γ : Context} (K : CAT Γ) {C D E T R : CAT Γ} (f : MAP C E) (g : MAP D E) where
  uncurryCone-restrict : (r : MAP R T) (s : Cone (funPost {C = K} f) (funPost {C = K} g) T)
    → ConeIdentification₁ (FunctorCones.uncurryCone K f g (cone-restrict r s))
        (cone-restrict (productMap r (id K)) (FunctorCones.uncurryCone K f g s))
  uncurryCone-restrict = FunctorConeRestriction.comparison K f g
```
