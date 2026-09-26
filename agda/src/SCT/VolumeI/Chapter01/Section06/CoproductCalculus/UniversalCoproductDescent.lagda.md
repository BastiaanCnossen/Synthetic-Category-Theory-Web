# Descent from two specified pullback squares

If two maps cover the base by a coproduct equivalence, their pullbacks
cover the total category. This form of coproduct descent accepts arbitrary
universal cones and returns the equivalence for their actual inclusions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter01.Section06.CoproductCalculus.UniversalCoproductDescent
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.CoproductCalculus.CoproductDescentSquare 𝒯 M B P U

module Cover {C D E T X Y : CAT} (f : MAP C E) (g : MAP D E) (h : MAP T E)
  (s : Cone f h X) (t : Cone g h Y)
  (es : IsPullback s) (et : IsPullback t) (e : IsEquiv (copair f g)) where

  module Descent = DescentSquare f g h
  canonical : MAP (Pullback f h ⊔ Pullback g h) T
  canonical = copair pullback₂ pullback₂

  canonical-isEquiv : IsEquiv canonical
  canonical-isEquiv = degenerate-pullback-converse e (coneSwap Descent.square)
    (pullback-swap Descent.square Descent.square-isPullback)

  comparison : (canonical ∘ coproductMap (pullbackLift s) (pullbackLift t)) =₁
    (copair (Cone.right s) (Cone.right t))
  comparison = copair-cong
    (pullbackLift-β₂ s ∙ copair-pre₁ pullback₂ pullback₂ (pullbackLift s))
    (pullbackLift-β₂ t ∙ copair-pre₂ pullback₂ pullback₂ (pullbackLift t)) ∙
      copair-post (in₁ ∘ pullbackLift s) (in₂ ∘ pullbackLift t) canonical

  copair-isEquiv : IsEquiv (copair (Cone.right s) (Cone.right t))
  copair-isEquiv = equiv-transport comparison
    (equiv-compose (coproductMap (pullbackLift s) (pullbackLift t)) canonical
      (coproductMap-isEquiv (pullbackLift s) (pullbackLift t) es et) canonical-isEquiv)
```
