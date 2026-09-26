# Composition of functor-category restrictions after evaluation

The restriction compositor is evaluated by pasting the two separation
squares. The parameter-change comparison supplies the inner edge, and
the mixed product composition law supplies the outer edge.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunPrecompositionCompositionBase as Base
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunPrecompositionParameterChange as Parameter
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunPrecompositionCompositeImage as Image
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunPrecompositionComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.RestrictionMate 𝒯 using (cancel-trailing-pair; prefix-transfer; cancel-prefix; close-comparison)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductMixedSubstitution 𝒯 M using (separate-composition)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; cancel-right; move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at; whisker-mixed-at)

module CompositorEvaluation {X A B C E : CAT} (f : MAP A B) (g : MAP B C) (h : MAP X (Fun C E)) where
  open Base.CompositorEvaluation 𝒯 M ℱ P f g h public

  χX = productRestriction-comp X f g
  χY = productRestriction-comp Y f g
  Xgf = productRestriction X (g ∘ f)
  Ygf = productRestriction Y (g ∘ f)
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

  leading = leading-prefix ∙ funPre-uncurry f Fg
  pasted-image = e ◁ paste (Shg ⁻¹) (Shf ⁻¹)

  abstract
    leading-transfer : ((projected-prefix ∙ pasted-image) ∙ z) =₂ ((leading ▷ HA) ∙ u₀)
    leading-transfer = isoComp-cong
      ((preWhisker-isoComp-at leading-prefix (funPre-uncurry f Fg) HA) ⁻¹) (idIso u₀) ∙
      prefix-transfer (leading-prefix ▷ HA) Pasted.target-evaluation projected-prefix pasted-image z
        (funPre-uncurry f Fg ▷ HA) u₀ output-endpoint core-transfer

  Sgf = productMap-separate h (g ∘ f)
  separation-image = e ◁ Sgf
  outer-associator = (comp-assoc Xgf HC e) ⁻¹
  product-composition = e ◁ (HC ◁ χX)
  prefix-associator = comp-assoc HA Ygf e
  prefix-composition = e ◁ (χY ▷ HA)

  abstract
    leading-normalization : Lifted.leading =₂ leading
    leading-normalization = (isoComp-assoc-at product-image
        (evaluation-associator ∙ evaluation-beta) (funPre-uncurry f Fg)) ⁻¹ ∙
      isoComp-cong (idIso product-image)
        ((isoComp-assoc-at evaluation-associator evaluation-beta (funPre-uncurry f Fg)) ⁻¹)

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
            ((postWhisker e ◁ separate-composition h f g) ∙
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
      (funPre-uncurry (g ∘ f) h ∙ funUncurryIso (preComp f g ▷ h)) =₂
      ((funUncurry h ◁ productRestriction-comp X f g) ∙
        (comp-assoc Xf Xg (funUncurry h) ∙
          ((funPre-uncurry g h ▷ Xf) ∙
            (funPre-uncurry f (funPre g ∘ h) ∙ funUncurryIso (comp-assoc h (funPre g) (funPre f))))))
    comparison = close-comparison _ Lifted.prefix projected-prefix pasted-image z
      ((leading ▷ HA) ∙ u₀) (outer-associator ∙ product-composition) _
      (isoComp-cong (idIso Lifted.prefix)
        (isoComp-cong (preWhisker HA ◁ leading-normalization) (idIso u₀)) ∙ Lifted.law)
      leading-transfer remove-prefix finish
```