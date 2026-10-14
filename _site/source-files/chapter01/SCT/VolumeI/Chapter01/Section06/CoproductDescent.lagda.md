# Descent for coproducts

The selected boundary changes, nested insertions and symmetry give the two
inclusions. Their copair is compared with the actual reassembly functor.
The complete inclusion comparisons retain the chosen matching; no agreement
with earlier higher proof witnesses is asserted.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.CoproductDescent where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_; _＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Equivalences
open import SCT.VolumeI.Chapter01.Section05.Coproducts
open import SCT.VolumeI.Chapter01.Section05.Copairing
open import SCT.VolumeI.Chapter01.Section05.CoproductConstructions
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeTransport using (cone-swap; cone-change-left)
open import SCT.VolumeI.Chapter01.Section06.ConePasting
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions
open import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange
open import SCT.VolumeI.Chapter01.Section06.NestedPullbacks

module _ {Γ : Context} where
  module Inclusion {C S E Z : CAT Γ} (i : MAP C S) (h : MAP S Z) (φ : MAP E Z)
    {f : MAP C Z} (α : f =₁ (h ∘ i)) where

    Total : CAT Γ
    Total = Pullback h φ
    p : MAP Total S
    p = pullback₁
    q : MAP Total E
    q = pullback₂
    module Change = ChangeLeftArrow α φ using (source; forward)
    module N = ChosenNested i h φ using (insert; insert-right; inner; inner-β; outer-cone)
    swap : MAP (Pullback i p) (Pullback p i)
    swap = pullback-swap i p
    inner : MAP (Pullback f φ) (Pullback i p)
    inner = N.insert ∘ Change.forward
    identify : MAP (Pullback f φ) (Pullback p i)
    identify = swap ∘ inner
    include : MAP (Pullback f φ) Total
    include = pullback₁ ∘ identify

    include-normal : include =₁ (N.inner ∘ Change.forward)
    include-normal = (N.insert-right ▷ Change.forward) ∙
      ((comp-assoc Change.forward N.insert pullback₂) ⁻¹ ∙
        ((pullback-factor-β₁ (cone-swap (pullback-cone i p)) ▷ inner) ∙
          (comp-assoc inner swap pullback₁) ⁻¹))

    direct-cone : Cone h φ (Pullback f φ)
    direct-cone = postcompose-cone-left i h (cone-change-left α Change.source)

    opaque
      include-cone-law : ConeIdentification₁ (cone-restrict include (pullback-cone h φ)) direct-cone
      include-cone-law = cone-compose
        (postcompose-cone-left-identification i h (pullback-factor-β (cone-change-left α Change.source)))
        (cone-compose (postcompose-cone-left-restrict i h Change.forward N.outer-cone)
          (cone-compose (cone-identification-restrict-One Change.forward N.inner-β)
            (cone-compose (cone-inverse (cone-restrict-assoc Change.forward N.inner (pullback-cone h φ)))
              (cone-action-One (pullback-cone h φ) include-normal))))

    include-β₁ : (p ∘ include) =₁ (i ∘ pullback₁ {f = f} {g = φ})
    include-β₁ = ConeIdentification₁.left include-cone-law

    include-β₂ : (q ∘ include) =₁ pullback₂ {f = f} {g = φ}
    include-β₂ = ConeIdentification₁.right include-cone-law

  module Descent {C D P Q : CAT Γ} (f : MAP C P) (g : MAP D P) (φ : MAP Q P) where

    combined : MAP (C ⊔ D) P
    combined = copair f g
    Total : CAT Γ
    Total = Pullback combined φ
    totalProjection : MAP Total (C ⊔ D)
    totalProjection = pullback₁
    module LeftBoundary = ChangeLeftArrow ((copair-β₁ f g) ⁻¹) φ using (forward; forward-isEquiv)
    module RightBoundary = ChangeLeftArrow ((copair-β₂ f g) ⁻¹) φ using (forward; forward-isEquiv)
    module LeftNesting = ChosenNested in₁ combined φ using (insert; insert-isEquiv)
    module RightNesting = ChosenNested in₂ combined φ using (insert; insert-isEquiv)

    identify₁ : MAP (Pullback f φ) (Pullback totalProjection in₁)
    identify₁ = pullback-swap in₁ totalProjection ∘ (LeftNesting.insert ∘ LeftBoundary.forward)

    identify₂ : MAP (Pullback g φ) (Pullback totalProjection in₂)
    identify₂ = pullback-swap in₂ totalProjection ∘ (RightNesting.insert ∘ RightBoundary.forward)

    opaque
      identify₁-isEquiv : IsEquiv identify₁
      identify₁-isEquiv = equiv-compose (LeftNesting.insert ∘ LeftBoundary.forward)
        (pullback-swap in₁ totalProjection)
        (equiv-compose LeftBoundary.forward LeftNesting.insert LeftBoundary.forward-isEquiv LeftNesting.insert-isEquiv)
        (pullback-swap-isEquiv in₁ totalProjection)

      identify₂-isEquiv : IsEquiv identify₂
      identify₂-isEquiv = equiv-compose (RightNesting.insert ∘ RightBoundary.forward)
        (pullback-swap in₂ totalProjection)
        (equiv-compose RightBoundary.forward RightNesting.insert RightBoundary.forward-isEquiv RightNesting.insert-isEquiv)
        (pullback-swap-isEquiv in₂ totalProjection)

    include₁ : MAP (Pullback f φ) Total
    include₁ = pullback₁ ∘ identify₁
    include₂ : MAP (Pullback g φ) Total
    include₂ = pullback₁ ∘ identify₂

    private
      module LeftProjection = ChosenNested in₁ combined φ
        using (inner; inner-right; insert-right)
      module RightProjection = ChosenNested in₂ combined φ
        using (inner; inner-right; insert-right)

      left-inner : MAP (Pullback f φ) (Pullback in₁ totalProjection)
      left-inner = LeftNesting.insert ∘ LeftBoundary.forward
      right-inner : MAP (Pullback g φ) (Pullback in₂ totalProjection)
      right-inner = RightNesting.insert ∘ RightBoundary.forward

      include₁-normal : include₁ =₁ (LeftProjection.inner ∘ LeftBoundary.forward)
      include₁-normal = (LeftProjection.insert-right ▷ LeftBoundary.forward) ∙
        ((comp-assoc LeftBoundary.forward LeftNesting.insert pullback₂) ⁻¹ ∙
          ((pullback-factor-β₁ (cone-swap (pullback-cone in₁ totalProjection)) ▷ left-inner) ∙
            (comp-assoc left-inner (pullback-swap in₁ totalProjection) pullback₁) ⁻¹))

      include₂-normal : include₂ =₁ (RightProjection.inner ∘ RightBoundary.forward)
      include₂-normal = (RightProjection.insert-right ▷ RightBoundary.forward) ∙
        ((comp-assoc RightBoundary.forward RightNesting.insert pullback₂) ⁻¹ ∙
          ((pullback-factor-β₁ (cone-swap (pullback-cone in₂ totalProjection)) ▷ right-inner) ∙
            (comp-assoc right-inner (pullback-swap in₂ totalProjection) pullback₁) ⁻¹))

      left-forward-right :
        (pullback₂ {f = combined ∘ in₁} {g = φ} ∘ LeftBoundary.forward) =₁
          pullback₂ {f = f} {g = φ}
      left-forward-right = pullback-factor-β₂
        (cone-change-left ((copair-β₁ f g) ⁻¹) (pullback-cone f φ))

      right-forward-right :
        (pullback₂ {f = combined ∘ in₂} {g = φ} ∘ RightBoundary.forward) =₁
          pullback₂ {f = g} {g = φ}
      right-forward-right = pullback-factor-β₂
        (cone-change-left ((copair-β₂ f g) ⁻¹) (pullback-cone g φ))

    opaque
      include₁-β₂ :
        (pullback₂ {f = combined} {g = φ} ∘ include₁) =₁ pullback₂ {f = f} {g = φ}
      include₁-β₂ = left-forward-right ∙
        ((LeftProjection.inner-right ▷ LeftBoundary.forward) ∙
          ((comp-assoc LeftBoundary.forward LeftProjection.inner pullback₂) ⁻¹ ∙
            (pullback₂ ◁ include₁-normal)))

      include₂-β₂ :
        (pullback₂ {f = combined} {g = φ} ∘ include₂) =₁ pullback₂ {f = g} {g = φ}
      include₂-β₂ = right-forward-right ∙
        ((RightProjection.inner-right ▷ RightBoundary.forward) ∙
          ((comp-assoc RightBoundary.forward RightProjection.inner pullback₂) ⁻¹ ∙
            (pullback₂ ◁ include₂-normal)))

    descent : MAP (Pullback f φ ⊔ Pullback g φ) Total
    descent = copair include₁ include₂

    reassembly-law :
      (reassemble totalProjection ∘ coproductMap identify₁ identify₂) =₁ descent
    reassembly-law = copair-cong (copair-pre₁ pullback₁ pullback₁ identify₁) (copair-pre₂ pullback₁ pullback₁ identify₂) ∙
      copair-post (in₁ ∘ identify₁) (in₂ ∘ identify₂) (reassemble totalProjection)

    opaque
      descent-isEquiv : IsEquiv descent
      descent-isEquiv = equiv-transport reassembly-law
        (equiv-compose (coproductMap identify₁ identify₂) (reassemble totalProjection)
          (coproductMap-isEquiv identify₁ identify₂ identify₁-isEquiv identify₂-isEquiv)
          (reassemble-isEquiv totalProjection))
```
