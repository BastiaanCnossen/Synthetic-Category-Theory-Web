# Higher reflection with prescribed projection images

A full higher cone comparison lifts to an identification of the original
identifications. Use the lifting theorem for the universal comparison
cone, retaining both projection computations. These computations matter
when the second projection carries a specified triangle over a base.

The chosen lift below need not agree with the choice in
`HigherConeReflection.Reflection.reflect`. Its prescribed images are
proved directly, without comparing those two choices.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackComparison as Comparison

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.HigherLifting
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.UniversalConeLifting 𝒯 P using (module UniversalLift)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.HigherReflection 𝒯 P
  using (module Encoded; module Reflection)

module Images {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s t : Cone f g T) where
  module Enc = Encoded s t

  opaque
    unfolding Enc.reflect-decoding Enc.normalization Enc.comparison
    left-image : {z z′ : Cone Enc.E.leftMap Enc.E.rightMap One}
      (Ξ : ConeIso₂ (Enc.E.decode z) (Enc.E.decode z′)) →
      ConeIso.leftIso (Enc.reflect-decoding {z = z} {z′ = z′} Ξ) =₃ ConeIso₂.leftId Ξ
    left-image {z} Ξ = isoComp-unitʳ-at (ConeIso₂.leftId Ξ) ∙
      (isoComp-cong (idIso (ConeIso₂.leftId Ξ)) (inverse-identity (Cone.left z)) ∙
        isoComp-unitˡ-at (ConeIso₂.leftId Ξ ∙ (idIso (Cone.left z)) ⁻¹))

    right-image : {z z′ : Cone Enc.E.leftMap Enc.E.rightMap One}
      (Ξ : ConeIso₂ (Enc.E.decode z) (Enc.E.decode z′)) →
      ConeIso.rightIso (Enc.reflect-decoding {z = z} {z′ = z′} Ξ) =₃ ConeIso₂.rightId Ξ
    right-image {z} Ξ = isoComp-unitʳ-at (ConeIso₂.rightId Ξ) ∙
      (isoComp-cong (idIso (ConeIso₂.rightId Ξ)) (inverse-identity (Cone.right z)) ∙
        isoComp-unitˡ-at (ConeIso₂.rightId Ξ ∙ (idIso (Cone.right z)) ⁻¹))

module Lifting {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (h k : MAP T (Pullback f g)) {α β : h =₁ k}
  (Ξ : ConeIso₂ (Reflection.induced-cone h k α) (Reflection.induced-cone h k β)) where
  module Compared = Comparison.IsoComparison 𝒯 dataPullback h k using (comparisonCone)
  module Enc = Encoded (conePre h (pullbackCone f g)) (conePre k (pullbackCone f g))
    using (reflect-decoding)
  module Computation = Images (conePre h (pullbackCone f g)) (conePre k (pullbackCone f g))
    using (left-image; right-image)
  module Chosen = UniversalLift Compared.comparisonCone (pullback-isoMap-isEquiv h k) α β
    (Enc.reflect-decoding {z = conePre α Compared.comparisonCone}
      {z′ = conePre β Compared.comparisonCone} Ξ) using (lift; left-image; right-image)

  opaque
    lift : α =₂ β
    lift = Chosen.lift

    left-image : (postWhisker (pullback₁ {f = f} {g}) ◁ lift) =₃ ConeIso₂.leftId Ξ
    left-image = Computation.left-image Ξ ∙ Chosen.left-image

    right-image : (postWhisker (pullback₂ {f = f} {g}) ◁ lift) =₃ ConeIso₂.rightId Ξ
    right-image = Computation.right-image Ξ ∙ Chosen.right-image
```
