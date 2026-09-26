# Transposition and successive restrictions

Transposition preserves successive restrictions. The pasted symmetry squares retain the product compositor and the original associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.TranspositionCompositionBase as Base
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.TranspositionCompositeImage as Image
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.TranspositionComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.RestrictionMate 𝒯 using (cancel-trailing-pair; prefix-transfer; cancel-prefix; close-comparison)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.Transposition 𝒯 M ℱ
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.SwapRestrictionComposition as SwapComposition
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
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
  projected-prefix = (comp-assoc HA Ygf e) ⁻¹ ∙ (e ◁ (χY ▷ HA))

  abstract
    prefix-cancellation :
      (leading-prefix ∙ ((β ⁻¹ ▷ Yf) ∙ evaluation-associator ⁻¹)) =₂ product-image
    prefix-cancellation = cancel-trailing-pair product-image evaluation-associator evaluation-beta
      (β ⁻¹ ▷ Yf) (pre-inverse β Yf)

    output-endpoint : projected-prefix =₂ ((leading-prefix ▷ HA) ∙ Pasted.target-evaluation)
    output-endpoint = normalize ⁻¹ ∙
      move-square (comp-assoc HA Ygf e) (product-image ▷ HA) (e ◁ (χY ▷ HA))
        (comp-assoc HA (Yg ∘ Yf) e) (whisker-mixed-at χY HA e)
      where
      q : (e ∘ (Yg ∘ Yf)) =₁ (Uf ∘ Yf)
      q = (β ⁻¹ ▷ Yf) ∙ evaluation-associator ⁻¹
      final : (e ∘ ((Yg ∘ Yf) ∘ HA)) =₁ ((e ∘ (Yg ∘ Yf)) ∘ HA)
      final = (comp-assoc HA (Yg ∘ Yf) e) ⁻¹
      normalize : ((leading-prefix ▷ HA) ∙ Pasted.target-evaluation) =₂
        ((product-image ▷ HA) ∙ final)
      normalize = isoComp-cong
        ((preWhisker HA ◁ prefix-cancellation) ∙ (preWhisker-isoComp-at leading-prefix q HA) ⁻¹)
        (idIso final) ∙ (isoComp-assoc-at (leading-prefix ▷ HA) (q ▷ HA) final) ⁻¹

  leading = leading-prefix ∙ μ
  pasted-image = e ◁ paste (Shg ⁻¹) (Shf ⁻¹)

  abstract
    leading-transfer : ((projected-prefix ∙ pasted-image) ∙ z) =₂ (leading ▷ HA)
    leading-transfer = (preWhisker-isoComp-at leading-prefix μ HA) ⁻¹ ∙
      (isoComp-unitʳ-at ((leading-prefix ▷ HA) ∙ (μ ▷ HA)) ∙
        prefix-transfer (leading-prefix ▷ HA) Pasted.target-evaluation projected-prefix pasted-image z
          (μ ▷ HA) (idIso _) output-endpoint
          ((isoComp-unitʳ-at (μ ▷ HA)) ⁻¹ ∙ core-transfer))
  Sgf = swap-restriction {X} (g ∘ f)
  separation-image = e ◁ Sgf
  outer-associator = (comp-assoc Xgf HC e) ⁻¹
  product-composition = e ◁ (HC ◁ χX)
  prefix-associator = comp-assoc HA Ygf e
  prefix-composition = e ◁ (χY ▷ HA)

  abstract
    leading-normalization : Lifted.leading =₂ leading
    leading-normalization = (isoComp-assoc-at product-image
        (evaluation-associator ∙ evaluation-beta) (μ)) ⁻¹ ∙
      isoComp-cong (idIso product-image)
        ((isoComp-assoc-at evaluation-associator evaluation-beta (μ)) ⁻¹)

    product-square :
      (separation-image ∙ (prefix-composition ∙ pasted-image)) =₂ product-composition
    product-square =
      isoComp-unitˡ-at product-composition ∙
      (isoComp-cong
        (postWhisker-idIso e (HC ∘ Xgf) ∙
          ((postWhisker e ◁ isoComp-inverseʳ-at Sgf) ∙
            (postWhisker-isoComp-at e Sgf (Sgf ⁻¹)) ⁻¹))
        (idIso product-composition) ∙
      ((isoComp-assoc-at separation-image (e ◁ Sgf ⁻¹) product-composition) ⁻¹ ∙
        isoComp-cong (idIso separation-image)
          (postWhisker-isoComp-at e (Sgf ⁻¹) (HC ◁ χX) ∙
            ((postWhisker e ◁ SwapComposition.Composite.comparison 𝒯 M {X} f g) ∙
              (postWhisker-isoComp-at e (χY ▷ HA) (paste (Shg ⁻¹) (Shf ⁻¹))) ⁻¹))))

    remove-prefix : (Lifted.prefix ∙ (projected-prefix ∙ pasted-image)) =₂
      (outer-associator ∙ product-composition)
    remove-prefix = cancel-prefix outer-associator separation-image prefix-associator
      prefix-composition pasted-image product-composition product-square

    outer-square : (outer-associator ∙ product-composition) =₂
      ((U ◁ χX) ∙ a₃ ⁻¹)
    outer-square = move-square (comp-assoc Xgf HC e) (U ◁ χX) product-composition a₃
      (postWhisker-comp-at χX HC e)

    finish : ((outer-associator ∙ product-composition) ∙ z) =₂
      ((U ◁ χX) ∙ (a₂ ∙ (a₁ ∙ r)))
    finish = isoComp-cong (idIso (U ◁ χX)) (cancel-left a₃ (a₂ ∙ (a₁ ∙ r))) ∙
      (isoComp-assoc-at (U ◁ χX) (a₃ ⁻¹) z ∙ isoComp-cong outer-square (idIso z))

    comparison :
      (transpose-pre (g ∘ f) h ∙ transposeIso (comp-assoc f g h)) =₂
      ((transpose h ◁ productRestriction-comp X f g) ∙
        (comp-assoc Xf Xg (transpose h) ∙
          ((transpose-pre g h ▷ Xf) ∙ transpose-pre f (h ∘ g))))
    comparison = close-comparison _ Lifted.prefix projected-prefix pasted-image z
      (leading ▷ HA) (outer-associator ∙ product-composition) _
      (isoComp-cong (idIso Lifted.prefix) (preWhisker HA ◁ leading-normalization) ∙ Lifted.law)
      leading-transfer remove-prefix finish
```