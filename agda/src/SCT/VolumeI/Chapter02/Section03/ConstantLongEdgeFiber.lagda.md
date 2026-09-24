# Taking the fiber at identity arrows

Paste a pullback cone with the pullback imposing a constant long edge.
The outer boundary is the endpoint of an identity arrow, hence an
equivalence. The remaining projection is therefore an equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section03.ConstantLongEdgeFiber
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)

module At {B C E T : CAT} (endpoint : MAP E C) (constant : MAP C E)
  (ε : (endpoint ∘ constant) =₁ (id C)) {b : MAP B C}
  (t : Cone endpoint b T) (et : IsPullback t) where
  private
    h = Cone.left t
    inner = coneSwap (pullbackCone h constant)
    module Paste = Pasting constant endpoint b t et
    outer = Paste.Paste.flatten inner

  projection-isEquiv : IsEquiv (Cone.right t ∘ pullback₁ {f = h} {constant})
  projection-isEquiv = degenerate-pullback-converse
    (equiv-transport (ε ⁻¹) (id-isEquiv C)) (coneSwap outer)
    (pullback-swap outer
      (Paste.paste-isPullback inner (pullback-swap (pullbackCone h constant)
        (pullbackCone-isPullback h constant))))
```
