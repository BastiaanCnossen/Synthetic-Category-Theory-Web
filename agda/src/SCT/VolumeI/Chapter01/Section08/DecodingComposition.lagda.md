# Decoding and successive restrictions

We restrict the evaluated compositor along the terminal-product inclusion.
Its composition law identifies the pasted boundary, with the original
external associator retained on the input side.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section08.DecodingCompositionBase as Base
import SCT.VolumeI.Chapter01.Section03.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section08.UnitRestrictionComposition as UnitComposition
import SCT.VolumeI.Chapter01.Section08.DecodingCompositeImage as Image
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.DecodingComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.RestrictionMate 𝒯 using (cancel-trailing-pair; prefix-transfer; cancel-prefix; close-comparison)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section03.DecodingNaturality 𝒯 M using (decodePre; oneProduct-natural)
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)
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
  projected-prefix = invIso (comp-assoc HA Ygf e) ∙ (e ◁ (χY ▷ HA))

  abstract
    prefix-cancellation : =₂
      (leading-prefix ∙ ((invIso β ▷ Yf) ∙ invIso evaluation-associator)) product-image
    prefix-cancellation = cancel-trailing-pair product-image evaluation-associator evaluation-beta
      (invIso β ▷ Yf) (pre-inverse β Yf)

    output-endpoint : =₂ projected-prefix ((leading-prefix ▷ HA) ∙ Pasted.target-evaluation)
    output-endpoint = invIso normalize ∙
      move-square (comp-assoc HA Ygf e) (product-image ▷ HA) (e ◁ (χY ▷ HA))
        (comp-assoc HA (Yg ∘ Yf) e) (whisker-mixed-at χY HA e)
      where
      q : =₁ (e ∘ (Yg ∘ Yf)) (Uf ∘ Yf)
      q = (invIso β ▷ Yf) ∙ invIso evaluation-associator
      final : =₁ (e ∘ ((Yg ∘ Yf) ∘ HA)) ((e ∘ (Yg ∘ Yf)) ∘ HA)
      final = invIso (comp-assoc HA (Yg ∘ Yf) e)
      normalize : =₂ ((leading-prefix ▷ HA) ∙ Pasted.target-evaluation)
        ((product-image ▷ HA) ∙ final)
      normalize = isoComp-cong
        ((preWhisker HA ◁ prefix-cancellation) ∙ invIso (preWhisker-isoComp-at leading-prefix q HA))
        (idIso final) ∙ invIso (isoComp-assoc-at (leading-prefix ▷ HA) (q ▷ HA) final)

  leading = leading-prefix ∙ μ
  pasted-image = e ◁ paste (invIso Shg) (invIso Shf)

  abstract
    leading-transfer : =₂ ((projected-prefix ∙ pasted-image) ∙ z) ((leading ▷ HA) ∙ u₀)
    leading-transfer = isoComp-cong
      (invIso (preWhisker-isoComp-at leading-prefix (μ) HA)) (idIso u₀) ∙
      prefix-transfer (leading-prefix ▷ HA) Pasted.target-evaluation projected-prefix pasted-image z
        (μ ▷ HA) u₀ output-endpoint core-transfer

  Sgf = oneProduct-natural (g ∘ f)
  separation-image = e ◁ Sgf
  outer-associator = invIso (comp-assoc Xgf HC e)
  product-composition = idIso (e ∘ (HC ∘ (g ∘ f)))
  prefix-associator = comp-assoc HA Ygf e
  prefix-composition = e ◁ (χY ▷ HA)

  abstract
    leading-normalization : =₂ Lifted.leading leading
    leading-normalization = invIso (isoComp-assoc-at product-image
        (evaluation-associator ∙ evaluation-beta) (μ)) ∙
      isoComp-cong (idIso product-image)
        (invIso (isoComp-assoc-at evaluation-associator evaluation-beta (μ)))

    product-square : =₂
      (separation-image ∙ (prefix-composition ∙ pasted-image)) product-composition
    product-square = postWhisker-idIso e (HC ∘ (g ∘ f)) ∙
      ((postWhisker e ◁ isoComp-inverseʳ-at Sgf) ∙
      (invIso (postWhisker-isoComp-at e Sgf (invIso Sgf)) ∙
        isoComp-cong (idIso separation-image)
          ((postWhisker e ◁ UnitComposition.Composite.comparison 𝒯 M f g) ∙
            invIso (postWhisker-isoComp-at e (χY ▷ HA) (paste (invIso Shg) (invIso Shf))))))
    remove-prefix : =₂ (Lifted.prefix ∙ (projected-prefix ∙ pasted-image))
      (outer-associator ∙ product-composition)
    remove-prefix = cancel-prefix outer-associator separation-image prefix-associator
      prefix-composition pasted-image product-composition product-square

    finish : =₂ ((outer-associator ∙ product-composition) ∙ z)
      (a₂ ∙ (a₁ ∙ r))
    finish = cancel-left a₃ (a₂ ∙ (a₁ ∙ r)) ∙
      isoComp-cong (isoComp-unitʳ-at outer-associator) (idIso z)

    comparison : =₂
      (decodePre (g ∘ f) h ∙ decodeMapIso (mapPre-comp f g ▷ h))
      (comp-assoc f g (decodeMap h) ∙
        ((decodePre g h ▷ f) ∙
          (decodePre f (mapPre g ∘ h) ∙ decodeMapIso (comp-assoc h (mapPre g) (mapPre f)))))
    comparison = close-comparison _ Lifted.prefix projected-prefix pasted-image z
      ((leading ▷ HA) ∙ u₀) (outer-associator ∙ product-composition) _
      (isoComp-cong (idIso Lifted.prefix)
        (isoComp-cong (preWhisker HA ◁ leading-normalization) (idIso u₀)) ∙ Lifted.law)
      leading-transfer remove-prefix finish
```
