# Decoding and successive restrictions

We restrict the evaluated compositor along the terminal-product inclusion.
Its composition law identifies the pasted boundary, with the original
external associator retained on the input side.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodingCompositionBase as Base
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.UnitRestrictionComposition as UnitComposition
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodingCompositeImage as Image
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodingComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.RestrictionMate 𝒯 using (cancel-trailing-pair; prefix-transfer; cancel-prefix; close-comparison)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section04.Substitution.DecodingNaturality 𝒯 M using (decodePre; oneProduct-natural)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; cancel-right; move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at; whisker-mixed-at)

module CompositorEvaluation {A B C E : CAT} (f : MAP A B) (g : MAP B C) (h : Obj-abs (Map C E)) where
  open Base.CompositorEvaluation 𝒯 M f g h public
  module Lifted = Image.CompositorImage 𝒯 M f g h


  χY = productRestriction-comp One f g
  Xgf = g ∘ f
  Ygf = productRestriction One (g ∘ f)
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
    leading-transfer : ((projected-prefix ∙ pasted-image) ∙ z) =₂ ((leading ▷ HA) ∙ u₀)
    leading-transfer = isoComp-cong
      ((preWhisker-isoComp-at leading-prefix (μ) HA) ⁻¹) (idIso u₀) ∙
      prefix-transfer (leading-prefix ▷ HA) Pasted.target-evaluation projected-prefix pasted-image z
        (μ ▷ HA) u₀ output-endpoint core-transfer

  Sgf = oneProduct-natural (g ∘ f)
  separation-image = e ◁ Sgf
  outer-associator = (comp-assoc Xgf HC e) ⁻¹
  product-composition = idIso (e ∘ (HC ∘ (g ∘ f)))
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
    product-square = postWhisker-idIso e (HC ∘ (g ∘ f)) ∙
      ((postWhisker e ◁ isoComp-inverseʳ-at Sgf) ∙
      ((postWhisker-isoComp-at e Sgf (Sgf ⁻¹)) ⁻¹ ∙
        isoComp-cong (idIso separation-image)
          ((postWhisker e ◁ UnitComposition.Composite.comparison 𝒯 M f g) ∙
            (postWhisker-isoComp-at e (χY ▷ HA) (paste (Shg ⁻¹) (Shf ⁻¹))) ⁻¹)))
    remove-prefix : (Lifted.prefix ∙ (projected-prefix ∙ pasted-image)) =₂
      (outer-associator ∙ product-composition)
    remove-prefix = cancel-prefix outer-associator separation-image prefix-associator
      prefix-composition pasted-image product-composition product-square

    finish : ((outer-associator ∙ product-composition) ∙ z) =₂
      (a₂ ∙ (a₁ ∙ r))
    finish = cancel-left a₃ (a₂ ∙ (a₁ ∙ r)) ∙
      isoComp-cong (isoComp-unitʳ-at outer-associator) (idIso z)

    comparison :
      (decodePre (g ∘ f) h ∙ decodeMapIso (mapPre-comp f g ▷ h)) =₂
      (comp-assoc f g (decodeMap h) ∙
        ((decodePre g h ▷ f) ∙
          (decodePre f (mapPre g ∘ h) ∙ decodeMapIso (comp-assoc h (mapPre g) (mapPre f)))))
    comparison = close-comparison _ Lifted.prefix projected-prefix pasted-image z
      ((leading ▷ HA) ∙ u₀) (outer-associator ∙ product-composition) _
      (isoComp-cong (idIso Lifted.prefix)
        (isoComp-cong (preWhisker HA ◁ leading-normalization) (idIso u₀)) ∙ Lifted.law)
      leading-transfer remove-prefix finish
```
