# Transposition and successive restrictions

Transposition preserves successive restrictions. The pasted symmetry squares retain the product compositor and the original associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section08.TranspositionCompositionBase as Base
import SCT.VolumeI.Chapter01.Section03.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section08.TranspositionCompositeImage as Image
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.TranspositionComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.RestrictionMate 𝒯 using (cancel-trailing-pair; prefix-transfer; cancel-prefix; close-comparison)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.Transposition 𝒯 M ℱ
import SCT.VolumeI.Chapter01.Section08.SwapRestrictionComposition as SwapComposition
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; cancel-right; move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at; whisker-mixed-at)

module CompositorEvaluation {X A B C E : CAT} (f : MAP A B) (g : MAP B C) (h : MAP C (Fun X E)) where
  open Base.CompositorEvaluation 𝒯 M ℱ f g h public
  module Lifted = Image.CompositorImage 𝒯 M ℱ f g h

  χX = productRestriction-comp X f g
  χY = slice-comparison {C = X} g f
  Xgf = productRestriction X (g ∘ f)
  Ygf = productMap (g ∘ f) (id X)
  product-image = e ◁ χY
  evaluation-associator = comp-assoc Yf Yg e
  evaluation-beta = β ▷ Yf
  leading-prefix = product-image ∙ (evaluation-associator ∙ evaluation-beta)
  projected-prefix = invIso (comp-assoc HA Ygf e) ∙ (e ◁ (χY ▷ HA))

  abstract
    prefix-cancellation : Iso₂
      (leading-prefix ∙ ((invIso β ▷ Yf) ∙ invIso evaluation-associator)) product-image
    prefix-cancellation = cancel-trailing-pair product-image evaluation-associator evaluation-beta
      (invIso β ▷ Yf) (pre-inverse β Yf)

    output-endpoint : Iso₂ projected-prefix ((leading-prefix ▷ HA) ∙ Pasted.target-evaluation)
    output-endpoint = invIso normalize ∙
      move-square (comp-assoc HA Ygf e) (product-image ▷ HA) (e ◁ (χY ▷ HA))
        (comp-assoc HA (Yg ∘ Yf) e) (whisker-mixed-at χY HA e)
      where
      q : NatIso (e ∘ (Yg ∘ Yf)) (Uf ∘ Yf)
      q = (invIso β ▷ Yf) ∙ invIso evaluation-associator
      final : NatIso (e ∘ ((Yg ∘ Yf) ∘ HA)) ((e ∘ (Yg ∘ Yf)) ∘ HA)
      final = invIso (comp-assoc HA (Yg ∘ Yf) e)
      normalize : Iso₂ ((leading-prefix ▷ HA) ∙ Pasted.target-evaluation)
        ((product-image ▷ HA) ∙ final)
      normalize = isoComp-cong
        ((preWhisker HA ◁ prefix-cancellation) ∙ invIso (preWhisker-isoComp-at leading-prefix q HA))
        (idIso final) ∙ invIso (isoComp-assoc-at (leading-prefix ▷ HA) (q ▷ HA) final)

  leading = leading-prefix ∙ μ
  pasted-image = e ◁ paste (invIso Shg) (invIso Shf)

  abstract
    leading-transfer : Iso₂ ((projected-prefix ∙ pasted-image) ∙ z) (leading ▷ HA)
    leading-transfer = invIso (preWhisker-isoComp-at leading-prefix μ HA) ∙
      (isoComp-unitʳ-at ((leading-prefix ▷ HA) ∙ (μ ▷ HA)) ∙
        prefix-transfer (leading-prefix ▷ HA) Pasted.target-evaluation projected-prefix pasted-image z
          (μ ▷ HA) (idIso _) output-endpoint
          (invIso (isoComp-unitʳ-at (μ ▷ HA)) ∙ core-transfer))
  Sgf = swap-restriction {X} (g ∘ f)
  separation-image = e ◁ Sgf
  outer-associator = invIso (comp-assoc Xgf HC e)
  product-composition = e ◁ (HC ◁ χX)
  prefix-associator = comp-assoc HA Ygf e
  prefix-composition = e ◁ (χY ▷ HA)

  abstract
    leading-normalization : Iso₂ Lifted.leading leading
    leading-normalization = invIso (isoComp-assoc-at product-image
        (evaluation-associator ∙ evaluation-beta) (μ)) ∙
      isoComp-cong (idIso product-image)
        (invIso (isoComp-assoc-at evaluation-associator evaluation-beta (μ)))

    product-square : Iso₂
      (separation-image ∙ (prefix-composition ∙ pasted-image)) product-composition
    product-square =
      isoComp-unitˡ-at product-composition ∙
      (isoComp-cong
        (postWhisker-idIso e (HC ∘ Xgf) ∙
          ((postWhisker e ◁ isoComp-inverseʳ-at Sgf) ∙
            invIso (postWhisker-isoComp-at e Sgf (invIso Sgf))))
        (idIso product-composition) ∙
      (invIso (isoComp-assoc-at separation-image (e ◁ invIso Sgf) product-composition) ∙
        isoComp-cong (idIso separation-image)
          (postWhisker-isoComp-at e (invIso Sgf) (HC ◁ χX) ∙
            ((postWhisker e ◁ SwapComposition.Composite.comparison 𝒯 M {X} f g) ∙
              invIso (postWhisker-isoComp-at e (χY ▷ HA) (paste (invIso Shg) (invIso Shf)))))))

    remove-prefix : Iso₂ (Lifted.prefix ∙ (projected-prefix ∙ pasted-image))
      (outer-associator ∙ product-composition)
    remove-prefix = cancel-prefix outer-associator separation-image prefix-associator
      prefix-composition pasted-image product-composition product-square

    outer-square : Iso₂ (outer-associator ∙ product-composition)
      ((U ◁ χX) ∙ invIso a₃)
    outer-square = move-square (comp-assoc Xgf HC e) (U ◁ χX) product-composition a₃
      (postWhisker-comp-at χX HC e)

    finish : Iso₂ ((outer-associator ∙ product-composition) ∙ z)
      ((U ◁ χX) ∙ (a₂ ∙ (a₁ ∙ r)))
    finish = isoComp-cong (idIso (U ◁ χX)) (cancel-left a₃ (a₂ ∙ (a₁ ∙ r))) ∙
      (isoComp-assoc-at (U ◁ χX) (invIso a₃) z ∙ isoComp-cong outer-square (idIso z))

    comparison : Iso₂
      (transpose-pre (g ∘ f) h ∙ transposeIso (comp-assoc f g h))
      ((transpose h ◁ productRestriction-comp X f g) ∙
        (comp-assoc Xf Xg (transpose h) ∙
          ((transpose-pre g h ▷ Xf) ∙ transpose-pre f (h ∘ g))))
    comparison = close-comparison _ Lifted.prefix projected-prefix pasted-image z
      (leading ▷ HA) (outer-associator ∙ product-composition) _
      (isoComp-cong (idIso Lifted.prefix) (preWhisker HA ◁ leading-normalization) ∙ Lifted.law)
      leading-transfer remove-prefix finish
```