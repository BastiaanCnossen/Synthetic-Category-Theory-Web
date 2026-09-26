# Comparing pastings with a fixed boundary

Keep the right boundary of a vertical pasting fixed. Its action on
comparisons preserves identities, composites, and inverses. These
calculations apply inside identification animae as well, where they
transport the matching witness of a cone comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Cancellation

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.FixedBoundaryComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionRestrictionCalculus 𝒯 M
  using (module BinaryOperation)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (isoInverse-unique)
open Cancellation vocabulary terminal products productLaws composition vertical whiskering
  using () renaming (cancel-left to cancel-boundary)

module FixedRight {C D : CAT} {f g h : MAP C D} (b : f =₁ g) where
  module Binary = BinaryOperation (isoComp {f = f} {g} {h})
    using (act-Iso₂; act-comp; act-id)

  action : {x y : g =₁ h} → x =₂ y → (x ∙ b) =₂ (y ∙ b)
  action q = isoComp-cong q (idIso b)

  opaque
    congruence : {x y : g =₁ h} {q r : x =₂ y} → q =₃ r → action q =₃ action r
    congruence s = Binary.act-Iso₂ s (idIso (idIso b))

    identity : (x : g =₁ h) → action (idIso x) =₃ idIso (x ∙ b)
    identity x = Binary.act-id x b

    composite : {x y z : g =₁ h} (r : y =₂ z) (q : x =₂ y) →
      action (r ∙ q) =₃ (action r ∙ action q)
    composite r q = Binary.act-comp r q (idIso b) (idIso b) ∙
      Binary.act-Iso₂ (idIso (r ∙ q)) ((isoComp-unitˡ-at (idIso b)) ⁻¹)

    inverse : {x y : g =₁ h} (q : x =₂ y) → action (q ⁻¹) =₃ (action q) ⁻¹
    inverse {x} q = (isoInverse-unique (action q) (action (q ⁻¹))
      (identity x ∙ (congruence (isoComp-inverseˡ-at q) ∙ (composite (q ⁻¹) q) ⁻¹))) ⁻¹

-- Normalize before substituting the large named-cone boundaries.
module Normalize {C D : CAT} {f g : MAP C D} (b : f =₁ g) where
  module Right = FixedRight {h = g} b using (action; congruence; composite; inverse)

  module At {x : f =₁ g} {r s : g =₁ g}
    (q : r =₂ s) (unit : s =₂ idIso g) (base : x =₂ (r ∙ b)) (w : x =₂ b)
    (image : w =₃ (isoComp-unitˡ-at b ∙ (Right.action (unit ∙ q) ∙ base))) where
    encoded = Right.action (unit ⁻¹) ∙ ((isoComp-unitˡ-at b) ⁻¹ ∙ w)

    opaque
      encoded-normal : encoded =₃ (Right.action q ∙ base)
      encoded-normal = isoComp-cong (Right.congruence (cancel-boundary unit q)) (idIso base) ∙
        (isoComp-cong ((Right.composite (unit ⁻¹) (unit ∙ q)) ⁻¹) (idIso base) ∙
        ((isoComp-assoc-at (Right.action (unit ⁻¹)) (Right.action (unit ∙ q)) base) ⁻¹ ∙
        (isoComp-cong (idIso (Right.action (unit ⁻¹)))
          (cancel-boundary (isoComp-unitˡ-at b) (Right.action (unit ∙ q) ∙ base)) ∙
          isoComp-cong (idIso (Right.action (unit ⁻¹)))
            (isoComp-cong (idIso ((isoComp-unitˡ-at b) ⁻¹)) image))))

      square : base =₃ (Right.action (q ⁻¹) ∙ encoded)
      square = (cancel-boundary (Right.action q) base ∙
        (isoComp-cong (idIso ((Right.action q) ⁻¹)) encoded-normal ∙
          isoComp-cong (Right.inverse q) (idIso encoded))) ⁻¹
```
