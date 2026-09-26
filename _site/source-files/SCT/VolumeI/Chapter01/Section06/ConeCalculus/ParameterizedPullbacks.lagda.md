# Parameters preserve pullback cones

Adjoining a category parameter to the left leg of a pullback cone
again gives a pullback. Paste the product projection square with the
original square. The comparison below identifies the pasted matching
with the matching used for relative families.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.ParameterizedPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductSquares 𝒯 P using (module SecondFactor)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ParameterizedCones 𝒯 using (module Parameter)

module Parameters (X : CAT) {C S T Y : CAT} {f : MAP C T} {p : MAP S T}
  (s : Cone f p Y) (es : IsPullback s) where
  module Param = Parameter X s
  module Product = SecondFactor X (Cone.left s)
  module Paste = Pasting (pr₂ {X} {C}) f p s es
  left-square : Cone (pr₂ {X} {C}) (Cone.left s) (X × Y)
  left-square = record { left = Param.R ; right = pr₂ ; match = Param.β }
  abstract
    left-square-isPullback : IsPullback left-square
    left-square-isPullback = pullback-cone-invariant
      (cone-match-change _ _ _ _ (inverse-inverse Param.β))
      (pullback-swap Product.square Product.square-isPullback)

    matching : Cone.match (Paste.Paste.flatten left-square) =₂ Cone.match Param.cone
    matching = isoComp-cong (idIso Param.Z) (isoComp-assoc-at Param.d (Param.A ⁻¹) Param.rest) ∙
      isoComp-assoc-at Param.Z (Param.d ∙ Param.A ⁻¹) Param.rest

    isPullback : IsPullback Param.cone
    isPullback = pullback-cone-invariant (cone-match-change _ _ _ _ matching)
      (Paste.paste-isPullback left-square left-square-isPullback)
```
