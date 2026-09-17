# Composition of functor-category restrictions after evaluation

The restriction compositor is evaluated by pasting the two separation
squares. The parameter-change comparison supplies the inner edge, and
the mixed product composition law supplies the outer edge.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section08.FunPrecompositionCompositionBase as Base
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section08.FunPrecompositionParameterChange as Parameter
import SCT.VolumeI.Chapter01.Section08.FunPrecompositionCompositeImage as Image
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.FunPrecompositionComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.RestrictionMate 𝒯 using (cancel-trailing-pair; prefix-transfer; cancel-prefix; close-comparison)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductMixedSubstitution 𝒯 M using (separate-composition)
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)
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

  leading = leading-prefix ∙ funPre-uncurry f Fg
  pasted-image = e ◁ paste (invIso Shg) (invIso Shf)

  abstract
    leading-transfer : Iso₂ ((projected-prefix ∙ pasted-image) ∙ z) ((leading ▷ HA) ∙ u₀)
    leading-transfer = isoComp-cong
      (invIso (preWhisker-isoComp-at leading-prefix (funPre-uncurry f Fg) HA)) (idIso u₀) ∙
      prefix-transfer (leading-prefix ▷ HA) Pasted.target-evaluation projected-prefix pasted-image z
        (funPre-uncurry f Fg ▷ HA) u₀ output-endpoint core-transfer

  Sgf = productMap-separate h (g ∘ f)
  separation-image = e ◁ Sgf
  outer-associator = invIso (comp-assoc Xgf HC e)
  product-composition = e ◁ (HC ◁ χX)
  prefix-associator = comp-assoc HA Ygf e
  prefix-composition = e ◁ (χY ▷ HA)

  abstract
    leading-normalization : Iso₂ Lifted.leading leading
    leading-normalization = invIso (isoComp-assoc-at product-image
        (evaluation-associator ∙ evaluation-beta) (funPre-uncurry f Fg)) ∙
      isoComp-cong (idIso product-image)
        (invIso (isoComp-assoc-at evaluation-associator evaluation-beta (funPre-uncurry f Fg)))

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
            ((postWhisker e ◁ separate-composition h f g) ∙
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
      (funPre-uncurry (g ∘ f) h ∙ funUncurryIso (preComp f g ▷ h))
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