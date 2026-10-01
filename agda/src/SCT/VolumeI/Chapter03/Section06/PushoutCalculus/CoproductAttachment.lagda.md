# Adding a redundant boundary component to a pushout

Adjoin a summand on which the vertical map is the identity, then cancel
that coproduct pushout. This turns a single-side collapse into the
full boundary pushout used in a join. The final bottom map is the copair
of the original bottom map and the unchanged boundary component.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.Section06.PushoutCalculus.CoproductAttachment
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) (B : Coproducts.CoproductStructure 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section05.Copairing 𝒯 M B
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P using (Square; IsPushout)
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (squareCocone)
open import SCT.VolumeI.Chapter01.Section08.PushoutExtensions 𝒯 M P using (pushout-extension-property)
open import SCT.VolumeI.Chapter01.Section08.RecognizingPushouts 𝒯 M ℱ P using (cocone-extension→pushout)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.UniversalCoconePasting 𝒯 M P using (module UniversalPasting)
open import SCT.VolumeI.Chapter01.Section08.PushoutPasting 𝒯 M P using (module Pasting)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.CoproductPushouts 𝒯 M ℱ P B using (module Adjoin)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.CoconeUniversalTransport 𝒯 M ℱ P
  using (module Invariant; module ChangeTop; module Pasted)

module Attachment {A C X Y D : CAT} {u : MAP A X} {v : MAP A C}
  {r : MAP X Y} {s : MAP C Y} (original : Square u v r s)
  (universal : IsPushout original) (j : MAP D X) where
  module Left = Adjoin v D using (sum-map; square; isPushout)
  top = copair u j
  -- Results of `ChangeTop`, `UniversalPasting.LiftOuter`, `Pasting` and
  -- `Pasted` are used as ordinary functions with explicit arguments.
  private
    outer-value = ChangeTop.value (copair-β₁ u j) (squareCocone original)
      (pushout-extension-property original universal)
    outer-value-extensions = ChangeTop.extensions (copair-β₁ u j) (squareCocone original)
      (pushout-extension-property original universal)
  chosen : Cocone top Left.sum-map Y
  chosen = UniversalPasting.LiftOuter.value in₁ top Left.square Left.isPushout Y outer-value
  chosen-square : Square top Left.sum-map r (Cocone.right chosen)
  chosen-square = record { commute = Cocone.match chosen }
  abstract
    outer-extensions : CoconeExtensionProperty
      (squareCocone (Pasting.outer Left.square chosen-square Left.isPushout))
    outer-extensions = Invariant.extensions
      (coconeIso-compose (Pasted.comparison Left.square chosen-square)
        (coconeIso-inverse
          (UniversalPasting.LiftOuter.comparison in₁ top Left.square Left.isPushout Y outer-value)))
      outer-value-extensions
    chosen-isPushout : IsPushout chosen-square
    chosen-isPushout = Pasting.cancel-isPushout Left.square chosen-square Left.isPushout
      (cocone-extension→pushout (Pasting.outer Left.square chosen-square Left.isPushout)
        outer-extensions)

  bottom : MAP (C ⊔ D) Y
  bottom = copair s (r ∘ j)
  abstract
    first : (Cocone.right chosen ∘ in₁) =₁ s
    first = UniversalPasting.LiftOuter.β in₁ top Left.square Left.isPushout Y outer-value
    second : (Cocone.right chosen ∘ in₂) =₁ (r ∘ j)
    second = (r ◁ copair-β₂ u j) ∙
      (comp-assoc in₂ top r ∙
        ((UniversalPasting.LiftOuter.α in₁ top Left.square Left.isPushout Y outer-value ▷ in₂) ∙
          (Adjoin.second v D (Cocone.right chosen)) ⁻¹))
    bottom-comparison : Cocone.right chosen =₁ bottom
    bottom-comparison = coproduct-reflect _ bottom
      ((copair-β₁ s (r ∘ j)) ⁻¹ ∙ first) ((copair-β₂ s (r ∘ j)) ⁻¹ ∙ second)
  abstract
    cocone : Cocone top Left.sum-map Y
    cocone = coconeRetarget chosen r bottom (idIso r) bottom-comparison
    square : Square top Left.sum-map r bottom
    square = record { commute = Cocone.match cocone }
  abstract
    extensions : CoconeExtensionProperty cocone
    extensions = Invariant.extensions (coconeRetarget-β chosen r bottom (idIso r) bottom-comparison)
      (pushout-extension-property chosen-square chosen-isPushout)
    isPushout : IsPushout square
    isPushout = cocone-extension→pushout square extensions
```
