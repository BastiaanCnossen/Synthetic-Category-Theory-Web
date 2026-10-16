# Functors on morphisms and hom categories

A functor acts on interval diagrams by postcomposition. Evaluation at an
endpoint identifies this action with applying the functor to that endpoint.
Thus postcomposition carries a morphism family with specified source and
target to a family between their images.

The induced map between endpoint fibers is obtained by applying this operation
to the universal arrow. Its complete pullback computation law retains the
base functor and the endpoint matching. The usual map on hom categories is
the specialization to two absolute objects. No composition-preservation or
identity-preservation law is asserted by this construction.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.MorphismFunctor where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost; funPost-β)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; evAt; ev₀; ev₁; insert; module AtPoint; MorphismFamily)
open import SCT.VolumeI.Chapter02.Section01.HomAndSlices
  using (Hom; endpointMap; module EndpointFiber)

module _ {Γ : Context} where
  evAt-post : {I C D : CAT Γ} (a : MAP One I) (F : MAP C D)
    → (evAt a ∘ funPost F) =₁ (F ∘ evAt a)
  evAt-post {I} {C} {D} a F =
    comp-assoc (insert a) (funEval {C = I} {D = C}) F ∙
      ((funPost-β {C = I} F ▷ insert a) ∙
        AtPoint.uncurry-image {I = I} {C = D} a (funPost F))

  private
    image-frame : {P C D : CAT Γ} (F : MAP C D)
      (a : MAP One ([1] {Γ = Γ})) (h : MAP P (Ar C)) (f : MAP P C)
      → (evAt a ∘ h) =₁ f → (evAt a ∘ (funPost F ∘ h)) =₁ (F ∘ f)
    image-frame F a h f p = (F ◁ p) ∙
      (comp-assoc h (evAt a) F ∙
        ((evAt-post a F ▷ h) ∙ (comp-assoc h (funPost F) (evAt a)) ⁻¹))

  map-morphism-family : {P C D : CAT Γ} (F : MAP C D) {f g : MAP P C}
    → MorphismFamily f g → MorphismFamily (F ∘ f) (F ∘ g)
  map-morphism-family F {f} {g} α = record
    { arrow = funPost F ∘ MorphismFamily.arrow α
    ; source-frame = image-frame F zero (MorphismFamily.arrow α) f
        (MorphismFamily.source-frame α)
    ; target-frame = image-frame F one (MorphismFamily.arrow α) g
        (MorphismFamily.target-frame α) }

  private
    module FiberCoordinates {P C : CAT Γ} (f g : MAP P C) where
      private
        universal-arrow : MAP (EndpointFiber.category f g) (Ar C)
        universal-arrow = EndpointFiber.arrow f g
        universal-base : MAP (EndpointFiber.category f g) P
        universal-base = EndpointFiber.base f g
        universal-matching : (endpointMap C ∘ universal-arrow) =₁ (pair f g ∘ universal-base)
        universal-matching = EndpointFiber.matching f g

      family : MorphismFamily (f ∘ universal-base) (g ∘ universal-base)
      family = record
        { arrow = universal-arrow
        ; source-frame = (pair-β₁ f g ▷ universal-base) ∙
            ((comp-assoc universal-base (pair f g) pr₁) ⁻¹ ∙
              ((pr₁ ◁ universal-matching) ∙ (comp-assoc universal-arrow (endpointMap C) pr₁ ∙
                (pair-β₁ ev₀ ev₁ ▷ universal-arrow) ⁻¹)))
        ; target-frame = (pair-β₂ f g ▷ universal-base) ∙
            ((comp-assoc universal-base (pair f g) pr₂) ⁻¹ ∙
              ((pr₂ ◁ universal-matching) ∙ (comp-assoc universal-arrow (endpointMap C) pr₂ ∙
                (pair-β₂ ev₀ ev₁ ▷ universal-arrow) ⁻¹))) }

  module EndpointImage {P C D : CAT Γ} (F : MAP C D) (f g : MAP P C) where
    private
      source : CAT Γ
      source = EndpointFiber.category f g
      b : MAP source P
      b = EndpointFiber.base f g
      image : MorphismFamily (F ∘ (f ∘ b)) (F ∘ (g ∘ b))
      image = map-morphism-family F (FiberCoordinates.family f g)
      reframed : MorphismFamily ((F ∘ f) ∘ b) ((F ∘ g) ∘ b)
      reframed = record
        { arrow = MorphismFamily.arrow image
        ; source-frame = (comp-assoc b f F) ⁻¹ ∙ MorphismFamily.source-frame image
        ; target-frame = (comp-assoc b g F) ⁻¹ ∙ MorphismFamily.target-frame image }

    cone : Cone (endpointMap D) (pair (F ∘ f) (F ∘ g)) source
    cone = EndpointFiber.boundary-cone (F ∘ f) (F ∘ g) b reframed

    map : MAP source (EndpointFiber.category (F ∘ f) (F ∘ g))
    map = EndpointFiber.extension (F ∘ f) (F ∘ g) b reframed

    map-image : ConeIdentification₁
      (cone-restrict map (EndpointFiber.universal (F ∘ f) (F ∘ g))) cone
    map-image = EndpointFiber.extension-image (F ∘ f) (F ∘ g) b reframed

    arrow-image : (EndpointFiber.arrow (F ∘ f) (F ∘ g) ∘ map)
      =₁ (funPost F ∘ EndpointFiber.arrow f g)
    arrow-image = ConeIdentification₁.left map-image

    base-image : (EndpointFiber.base (F ∘ f) (F ∘ g) ∘ map) =₁ b
    base-image = ConeIdentification₁.right map-image

  map-hom : {C D : CAT Γ} (F : MAP C D) (x y : MAP One C)
    → MAP (Hom C x y) (Hom D (F ∘ x) (F ∘ y))
  map-hom F x y = EndpointImage.map F x y
```
