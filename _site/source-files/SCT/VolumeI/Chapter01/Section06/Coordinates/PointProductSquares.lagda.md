# Pulling a product back along a point

The graph of a constant functor is the pullback of the corresponding
product projection along the point. The comparison below retains the
projection matching, rather than only identifying the pullback category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as PU
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductSquares as Products

module SCT.VolumeI.Chapter01.Section06.Coordinates.PointProductSquares
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; conePre; IsPullback; pullback-cone-invariant;
         pullback-restrict-equivalence)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)

module Second (C : CAT) {D : CAT} (x : MAP One D) where
  module Product = Products.SecondFactor 𝒯 P C x
  private
    j = pair (id C) (terminate C)
    b = pair-β₂ (id C ∘ pr₁) (x ∘ pr₂)
    r = pair-β₂ (id C) (terminate C)
    A = comp-assoc j pr₂ x
    B = comp-assoc j (productMap (id C) x) pr₂
    U = (b ▷ j) ∙ B ⁻¹
    U′ = (((b ⁻¹) ⁻¹) ▷ j) ∙ B ⁻¹
    α = comp-unitˡ (id C) ∙
      ((id C ◁ pair-β₁ (id C) (terminate C)) ∙ comp-assoc j pr₁ (id C))
    β = (x ◁ r) ∙ A
    κ = pair-cong α β ∙ pair-pre (id C ∘ pr₁) (x ∘ pr₂) j

  square : Cone (pr₂ {C} {D}) x C
  square = record { left = pair (id C) (const x) ; right = terminate C
    ; match = pair-β₂ (id C) (const x) }

  restricted = conePre j (coneSwap Product.square)

  comparison : ConeIso restricted square
  comparison = record { leftIso = κ ; rightIso = r
    ; compatible = isoComp-cong (idIso (x ◁ r))
        (isoComp-cong (idIso A)
          (isoComp-cong (preWhisker j ◁ (inverse-inverse b) ⁻¹) (idIso (B ⁻¹)))) ∙
        (isoComp-assoc-at (x ◁ r) A U ∙
          pair-pre-cong-triangle₂ (id C ∘ pr₁) (x ∘ pr₂) j α β) }

  square-isPullback : IsPullback square
  square-isPullback = pullback-cone-invariant comparison
    (pullback-restrict-equivalence (coneSwap Product.square) j
      (pullback-swap Product.square Product.square-isPullback)
      (equiv-inverse (product-unitʳ-isEquiv C)))

module First {C : CAT} (x : MAP One C) (D : CAT) where
  module Product = Products.FirstFactor 𝒯 P x D
  private
    j = pair (terminate D) (id D)
    b = pair-β₁ (x ∘ pr₁) (id D ∘ pr₂)
    r = pair-β₁ (terminate D) (id D)
    A = comp-assoc j pr₁ x
    B = comp-assoc j (productMap x (id D)) pr₁
    U = (b ▷ j) ∙ B ⁻¹
    α = (x ◁ r) ∙ A
    β = comp-unitˡ (id D) ∙
      ((id D ◁ pair-β₂ (terminate D) (id D)) ∙ comp-assoc j pr₂ (id D))
    κ = pair-cong α β ∙ pair-pre (x ∘ pr₁) (id D ∘ pr₂) j

    j-isEquiv : IsEquiv j
    j-isEquiv = record { inverse = pr₂
      ; sectionIso = (pair-β₂ (terminate D) (id D)) ⁻¹
      ; retractionIso = (pair-iso (terminal-iso _ _)
          ((comp-unitʳ pr₂) ⁻¹ ∙
            (comp-unitˡ pr₂ ∙ project-pair₂ (terminate D) (id D) pr₂))) ⁻¹ }

  square : Cone (pr₁ {C} {D}) x D
  square = record { left = pair (const x) (id D) ; right = terminate D
    ; match = pair-β₁ (const x) (id D) }

  restricted = conePre j (coneSwap Product.square)

  comparison : ConeIso restricted square
  comparison = record { leftIso = κ ; rightIso = r
    ; compatible = isoComp-cong (idIso (x ◁ r))
        (isoComp-cong (idIso A)
          (isoComp-cong (preWhisker j ◁ (inverse-inverse b) ⁻¹) (idIso (B ⁻¹)))) ∙
        (isoComp-assoc-at (x ◁ r) A U ∙
          pair-pre-cong-triangle₁ (x ∘ pr₁) (id D ∘ pr₂) j α β) }

  square-isPullback : IsPullback square
  square-isPullback = pullback-cone-invariant comparison
    (pullback-restrict-equivalence (coneSwap Product.square) j
      (pullback-swap Product.square Product.square-isPullback) j-isEquiv)
```
