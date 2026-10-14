# Global relative functor categories

For categories `(C,p)` and `(D,q)` over `S`, the global relative functor
category is the fiber of postcomposition by `q` over the named functor `p`.
An arbitrary categorical family is a functor over `S` from
`(K × C,p ∘ pr₂)` to `(D,q)`. Its chosen factor retains the complete fiber
beta and the image of its selected matching under native evaluation.
This initial construction does not assert the two-way relative representation.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section09.RelativeFunctorCategories where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints; restore-boundaries)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying
open import SCT.VolumeI.Chapter01.Section07.Functoriality
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName; funName-β)

module RelativeFunctorCategory {Γ : Context} {S : CAT Γ}
  (A B : CategoryOverBase S) where
  private
    C = CategoryOverBase.category A
    D = CategoryOverBase.category B
    p = CategoryOverBase.map A
    q = CategoryOverBase.map B
    eD = funEval {C = C} {D = D}
    eS = funEval {C = C} {D = S}

  postcomposition : MAP (Fun C D) (Fun C S)
  postcomposition = funPost {C = C} q

  point : MAP One (Fun C S)
  point = funName p

  category : CAT Γ
  category = Pullback postcomposition point

  fiber : Cone postcomposition point category
  fiber = pullback-cone postcomposition point

  inclusion : MAP category (Fun C D)
  inclusion = Cone.left fiber

  family-source : (K : CAT Γ) → CategoryOverBase S
  family-source K = category-over (K × C) (p ∘ pr₂)

  Family : CAT Γ → Set m
  Family K = FunctorOverBase (family-source K) B

  named-evaluation : {K : CAT Γ} (z : MAP K One)
    → evaluate eS (point ∘ z) =₁ (p ∘ pr₂ {C = K} {D = C})
  named-evaluation z =
    (p ◁ (comp-unitˡ pr₂ ∙ pair-β₂ (z ∘ pr₁) (id C ∘ pr₂))) ∙
      (comp-assoc (productMap z (id C)) (pr₂ {C = One} {D = C}) p ∙
        ((funName-β p ▷ productMap z (id C)) ∙ evaluate-restrict eS point z))

  module ChosenFamily {K : CAT Γ} (F : Family K) where
    underlying = FunctorOverBase.functor F
    base-cell = FunctorOverBase.cell F
    curried = funCurry {C = C} {D = D} underlying
    curry-computation = funCurry-β {C = C} {D = D} underlying
    private
      post-change = funPost-uncurry {C = C} {D = D} {E = S} q curried
      point-change = named-evaluation (terminate K)
      desired = base-cell ∙ (q ◁ curry-computation)
      evaluated-matching = point-change ⁻¹ ∙ (desired ∙ post-change)

    encoded : Cone postcomposition point K
    encoded = record
      { left = curried; right = terminate K
      ; match = reflect eS (funUniversal C S)
          (postcomposition ∘ curried) (point ∘ terminate K) evaluated-matching }

    matching-image :
      changeEndpoints post-change point-change (evaluate-cong eS (Cone.match encoded)) =₂ desired
    matching-image = restore-boundaries post-change point-change desired
      (evaluate-cong eS (Cone.match encoded))
      (reflect-β-One eS (funUniversal C S)
        (postcomposition ∘ curried) (point ∘ terminate K) evaluated-matching)

    factor : MAP K category
    factor = pullback-factor encoded

    computation : ConeIdentification₁ (cone-restrict factor fiber) encoded
    computation = pullback-factor-β encoded

    underlying-computation : evaluate eD (inclusion ∘ factor) =₁ underlying
    underlying-computation = curry-computation ∙
      evaluate-cong eD (ConeIdentification₁.left computation)

  evaluated-family : {K : CAT Γ} → MAP K category → Family K
  evaluated-family {K} h = functor-over
    (evaluate eD (inclusion ∘ h))
    (changeEndpoints
      (funPost-uncurry {C = C} {D = D} {E = S} q (inclusion ∘ h))
      (named-evaluation (Cone.right fiber ∘ h))
      (evaluate-cong eS (Cone.match (cone-restrict h fiber))))

  module FamilyRecovery {X K : CAT Γ} (F G : Family K)
    (Φ : ConeIdentification X
      (cone-restrict (ChosenFamily.factor F) fiber)
      (cone-restrict (ChosenFamily.factor G) fiber)) where
    open Terms.Equalities X using (_＝_)
    private
      module R = PullbackRecovery (ChosenFamily.factor F) (ChosenFamily.factor G) Φ

    identification : ChosenFamily.factor F ＝ ChosenFamily.factor G
    identification = R.identification

    whole-image : ConeIdentificationEquality (cone-action fiber identification) Φ
    whole-image = R.recovery-law
```
