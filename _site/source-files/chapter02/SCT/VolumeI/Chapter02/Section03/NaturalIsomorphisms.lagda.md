# Conditional natural isomorphisms and full identification animae

The actual functor-category names induce an equivalence on identification
animae. Decode their native evaluation action, restrict along the terminal
insertion, and change endpoints by the chosen funName beta comparisons.
The inverse of this equivalence supplies the naming comparison with its
whole recovery equation.

The conditional Rezk fiber equivalence then identifies the full anima of
identifications between functors with the actual isomorphism fiber between
their names. Its complete cone computation retains the selected matching.
The Rezk hypothesis is explicit and no new assumption is introduced.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section03.NaturalIsomorphisms where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terms using (Equal)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-compose; equiv-inverse)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (product-unitˡ-inverse; product-unitˡ-pr₂-inverse; product-unitˡ-inverse-isEquiv)
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence using (preWhisker-isEquiv)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints₌; changeEndpoints₌-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; ConeIdentification₁; cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
  using (cone-compose; cone-inverse; cone-identification-restrict-One; cone-restrict-assoc)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks using (pullback-cone)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluation-action)
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation using (evaluation-action-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName; funName-β)
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms using (identityIso; isoEndpoints)
open import SCT.VolumeI.Chapter02.Section03.RezkFibers using (IsoBetween; module IdentificationFiber)

module IdentificationNames {Γ : Context} {C D : CAT Γ} (f g : MAP C D) where
  private
    evaluation : MAP (Fun C D × C) D
    evaluation = funEval
    terminal-insertion : MAP C (One × C)
    terminal-insertion = product-unitˡ-inverse C

    decoded-name : (q : MAP C D) →
      (funUncurry (funName q) ∘ terminal-insertion) =₁ q
    decoded-name q = comp-unitʳ q ∙
      ((q ◁ product-unitˡ-pr₂-inverse C) ∙
        (comp-assoc terminal-insertion pr₂ q ∙ (funName-β q ▷ terminal-insertion)))

    uncurrying-action : MAP (Equal (funName f) (funName g))
      (Equal (funUncurry (funName f)) (funUncurry (funName g)))
    uncurrying-action = evaluation-action evaluation (funName f) (funName g)

    uncurrying-action-isEquiv : IsEquiv uncurrying-action
    uncurrying-action-isEquiv = evaluation-action-isEquiv evaluation One (funUniversal C D One)
      (funName f) (funName g)

    restriction-action :
      MAP (Equal (funUncurry (funName f)) (funUncurry (funName g)))
        (Equal (funUncurry (funName f) ∘ terminal-insertion)
          (funUncurry (funName g) ∘ terminal-insertion))
    restriction-action = preWhisker terminal-insertion

    restriction-action-isEquiv : IsEquiv restriction-action
    restriction-action-isEquiv = preWhisker-isEquiv terminal-insertion
      (product-unitˡ-inverse-isEquiv C) (funUncurry (funName f)) (funUncurry (funName g))

  decoding : MAP (Equal (funName f) (funName g)) (Equal f g)
  decoding = changeEndpoints₌ (decoded-name f) (decoded-name g) ∘
    (restriction-action ∘ uncurrying-action)

  decoding-isEquiv : IsEquiv decoding
  decoding-isEquiv = equiv-compose (restriction-action ∘ uncurrying-action)
    (changeEndpoints₌ (decoded-name f) (decoded-name g))
    (equiv-compose uncurrying-action restriction-action
      uncurrying-action-isEquiv restriction-action-isEquiv)
    (changeEndpoints₌-isEquiv (decoded-name f) (decoded-name g))

  naming : MAP (Equal f g) (Equal (funName f) (funName g))
  naming = IsEquiv.inverse decoding-isEquiv

  naming-isEquiv : IsEquiv naming
  naming-isEquiv = equiv-inverse decoding-isEquiv

  recovery : (decoding ∘ naming) =₁ id (Equal f g)
  recovery = (IsEquiv.right-inverse-law decoding-isEquiv) ⁻¹

module _ {Γ : Context} where
  NatIsoBetween : {C D : CAT Γ} → MAP C D → MAP C D → CAT Γ
  NatIsoBetween f g = IsoBetween (funName f) (funName g)

  module NaturalIdentification {C D : CAT Γ}
    (R : IsEquiv (identityIso (Fun C D))) (f g : MAP C D) where
    module Names = IdentificationNames f g using (naming; naming-isEquiv; decoding; recovery)
    module Fiber = IdentificationFiber (Fun C D) R (funName f) (funName g)
      using (identification-to-iso; identification-to-iso-isEquiv; comparison-cone; comparison-image)

    identification-to-natural-iso : MAP (Equal f g) (NatIsoBetween f g)
    identification-to-natural-iso = Fiber.identification-to-iso ∘ Names.naming

    identification-to-natural-iso-isEquiv : IsEquiv identification-to-natural-iso
    identification-to-natural-iso-isEquiv = equiv-compose Names.naming Fiber.identification-to-iso
      Names.naming-isEquiv Fiber.identification-to-iso-isEquiv

    private
      point : MAP One (Fun C D × Fun C D)
      point = pair (funName f) (funName g)
      universal : Cone point (isoEndpoints (Fun C D)) (NatIsoBetween f g)
      universal = pullback-cone point (isoEndpoints (Fun C D))

    comparison-cone : Cone point (isoEndpoints (Fun C D)) (Equal f g)
    comparison-cone = cone-restrict Names.naming Fiber.comparison-cone

    comparison-image : ConeIdentification₁
      (cone-restrict identification-to-natural-iso universal) comparison-cone
    comparison-image = cone-compose
      (cone-identification-restrict-One Names.naming Fiber.comparison-image)
      (cone-inverse (cone-restrict-assoc Names.naming Fiber.identification-to-iso universal))
```
