# Associativity with normalized restriction coordinates

The two fully normalized triple restrictions agree. This combines the
product restriction associator with the coordinate pentagon, retaining
the literal nested target and both product projections.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductRestrictionAssociativity 𝒯 M using (restriction-assoc)
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionCompositeCoordinate as Composite
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionImage as Image
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionPentagon as Pentagon

module At {A B C D : CAT} (X : CAT) (f : MAP A B) (g : MAP B C) (h : MAP C D) where
  module Left = Composite.At 𝒯 M X f g h
  module Right = Image.At 𝒯 M X f g h
  module Coordinate = Pentagon.At 𝒯 X f g h
  Jf : MAP (X × A) (X × B)
  Jf = productMap (id X) f
  Jg : MAP (X × B) (X × C)
  Jg = productMap (id X) g
  Jh : MAP (X × C) (X × D)
  Jh = productMap (id X) h
  κfg = productRestriction-comp X f g
  κgh = productRestriction-comp X g h
  κfgh = productRestriction-comp X f (h ∘ g)
  κgfh = productRestriction-comp X (g ∘ f) h
  η = productMap-cong (idIso (id X)) (comp-assoc f g h)
  tail = (Jh ◁ κfg) ∙ comp-assoc Jf Jg Jh
  long = κfgh ∙ (κgh ▷ Jf)

  abstract
    value :
      (Left.Changed.normal ∙ ((Left.Changed.change ∙ κgh) ▷ Jf)) =₂
      (Right.ψ ∙ tail)
    value = isoComp-cong (Right.value ⁻¹) (idIso tail) ∙
      (isoComp-assoc-at Coordinate.right-frame κgfh tail) ⁻¹ ∙
      isoComp-cong (idIso Coordinate.right-frame) ((restriction-assoc X h g f) ⁻¹) ∙
      isoComp-assoc-at Coordinate.right-frame η long ∙
      isoComp-cong (Coordinate.value ⁻¹) (idIso long) ∙
      isoComp-assoc-at Coordinate.left-frame κfgh (κgh ▷ Jf) ∙
      isoComp-cong Left.value (idIso (κgh ▷ Jf)) ∙
      (isoComp-assoc-at Left.Changed.normal (Left.Changed.change ▷ Jf) (κgh ▷ Jf)) ⁻¹ ∙
      isoComp-cong (idIso Left.Changed.normal) (preWhisker-isoComp-at Left.Changed.change κgh Jf)
```
