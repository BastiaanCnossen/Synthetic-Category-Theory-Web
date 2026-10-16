# Point evaluation at the identity parameter

The actual left normalization used by point evaluation becomes its right
unitor at the identity parameter. Constants use terminal uniqueness, and
paired restriction uses its existing right-unit computation. This is the
left part of comparing the native uncurry identity triangle with the
original endpoint frame. The right part uses the original product-functor
identity and product-pair comparison; cancellation then gives the complete
identity normalization, with all selected triangles unchanged.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.PointEvaluationIdentity where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (terminal-unique₂)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (right-unitor-comp; identity-unitors; triangle-with-identity)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair⁼-cong)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction using (pair-pre-id)
open import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors using (binary-pre)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap; productMap-id)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairingIdentity using (module ProductPairingIdentity)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-id)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (evAt; insert; module AtPoint)

private
  module _ {Γ : Context} where
    constant-restriction-id : {P I : CAT Γ} (a : MAP One I)
      → const-pre {R = P} {X = P} a (id P) =₂ comp-unitʳ (const {P = P} a)
    constant-restriction-id {P} a = (right-unitor-comp (terminate P) a) ⁻¹ ∙
      comp₌-cong
        (postWhisker a ◁ terminal-unique₂
          (terminal-identification (terminate P ∘ id P) (terminate P))
          (comp-unitʳ (terminate P)))
        (id₌ (comp-assoc (id P) (terminate P) a))

    binary-restriction-id : {P A B C : CAT Γ} (e : MAP (A × B) C)
      (x : MAP P A) (y : MAP P B)
      → ((e ◁ pair⁼ (comp-unitʳ x) (comp-unitʳ y)) ∙ binary-pre e x y (id P)) =₂
        comp-unitʳ (e ∘ pair x y)
    binary-restriction-id {P} e x y = (right-unitor-comp (pair x y) e) ⁻¹ ∙
      (comp₌-cong (postWhisker e ◁ pair-pre-id x y)
        (id₌ (comp-assoc (id P) (pair x y) e)) ∙
      (comp₌-cong
        ((postWhisker-comp₌ e (pair⁼ (comp-unitʳ x) (comp-unitʳ y))
          (pair-pre x y (id P))) ⁻¹)
        (id₌ (comp-assoc (id P) (pair x y) e)) ∙
        (comp₌-assoc (e ◁ pair⁼ (comp-unitʳ x) (comp-unitʳ y))
          (e ◁ pair-pre x y (id P)) (comp-assoc (id P) (pair x y) e)) ⁻¹))

module PointEvaluationIdentity {Γ : Context} {I C : CAT Γ} (a : MAP One I) where
  private
    F : CAT Γ
    F = Fun I C
    e : MAP (F × I) C
    e = funEval
    left-normal : (evAt a ∘ id F) =₁ evAt a
    left-normal = (e ◁ pair⁼ (comp-unitˡ (id F)) (const-pre a (id F))) ∙
      binary-pre e (id F) (const {P = F} a) (id F)

  left-normalization : left-normal =₂ comp-unitʳ (evAt a)
  left-normalization = binary-restriction-id e (id F) (const a) ∙
    comp₌-cong
      (postWhisker e ◁ pair⁼-cong ((identity-unitors F) ⁻¹) (constant-restriction-id a))
      (id₌ (binary-pre e (id F) (const {P = F} a) (id F)))


  private
    i : MAP F (F × I)
    i = insert a
    J : MAP (F × I) (F × I)
    J = productMap (id F) (id I)
    kappa : J =₁ id (F × I)
    kappa = productMap-id F I
    pair-unit = pair⁼ (comp-unitˡ (id F)) (comp-unitˡ (const {P = F} a))
    pair-image = productMap-pair (id F) (id I) (id F) (const {P = F} a)
    associator = comp-assoc i J e
    module Structural = ProductPairingIdentity (id F) (const {P = F} a)
    right-normal : (funUncurry (id F) ∘ i) =₁ evAt a
    right-normal = (e ◁ pair⁼ (comp-unitʳ (id F)) (comp-unitˡ (const {P = F} a))) ∙
      ((e ◁ pair-image) ∙ associator)
    right₁ = comp₌-cong
      (postWhisker e ◁ pair⁼-cong (identity-unitors F)
        (id₌ (comp-unitˡ (const {P = F} a))))
      (id₌ ((e ◁ pair-image) ∙ associator))
    right₂ = (comp₌-assoc (e ◁ pair-unit) (e ◁ pair-image) associator) ⁻¹
    right₃ = comp₌-cong ((postWhisker-comp₌ e pair-unit pair-image) ⁻¹) (id₌ associator)
    right₄ = comp₌-cong (postWhisker e ◁ Structural.compatibility) (id₌ associator)
    right₅ = (triangle-with-identity e i J kappa) ⁻¹
    right₆ = (preWhisker-comp₌ (comp-unitʳ e) (e ◁ kappa) i) ⁻¹
    right-normalization : right-normal =₂ (evaluate-id e ▷ i)
    right-normalization = right₆ ∙ (right₅ ∙ (right₄ ∙ (right₃ ∙ (right₂ ∙ right₁))))

  identity-normalization :
    ((evaluate-id e ▷ insert a) ∙ AtPoint.uncurry-image a (id F)) =₂ comp-unitʳ (evAt a)
  identity-normalization = left-normalization ∙
    (comp-inv-left right-normal left-normal ∙
      comp₌-cong (right-normalization ⁻¹) (id₌ ((right-normal ⁻¹) ∙ left-normal)))
```
