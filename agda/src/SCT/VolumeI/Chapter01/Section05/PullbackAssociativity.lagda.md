# Associativity over a common base

The common-base associativity exercise follows by two nested-pullback
comparisons and symmetry. The final boundary change uses the specified
matching of the first two factors, so the result has the base map through
the first projection on both sides.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.PullbackAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section05.PullbackSymmetry 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.NestedPullbacks 𝒯 P using (module Nested)
open import SCT.VolumeI.Chapter01.Section05.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section05.CospanEquivalences 𝒯 P using (module CospanEquivalence)
open import SCT.VolumeI.Chapter01.Section05.PullbackArrowChange 𝒯 P using (module ChangeLeft)

module PullbackAssociativity {B C D E : CAT} (f : MAP B E) (g : MAP C E) (h : MAP D E) where

  CD = Pullback g h
  CB = Pullback g f
  BC = Pullback f g
  pCD : MAP CD C
  pCD = pb₁
  pCB : MAP CB C
  pCB = pb₁
  pBC : MAP BC B
  pBC = pb₁
  qBC : MAP BC C
  qBC = pb₂
  module First = Nested pCD g f
  module Second = Nested pCB g h

  swapCospan : CospanMap (g ∘ pCB) h (g ∘ qBC) h
  swapCospan = record
    { left = pullbackSwap g f ; right = id D ; base = id E
    ; leftSquare = invIso (comp-unitˡ (g ∘ pCB)) ∙
        ((g ◁ pbLift-β₂ (coneSwap (pbCone g f))) ∙ comp-assoc (pullbackSwap g f) qBC g)
    ; rightSquare = invIso (comp-unitˡ h) ∙ comp-unitʳ h }
  module Swap = CospanMap swapCospan
  module SwapEquiv = CospanEquivalence swapCospan (pullbackSwap-isEquiv g f) (id-isEquiv D) (id-isEquiv E)
  module Change = ChangeLeft (invIso (pbMatch {f = f} {g})) h

  first = First.insert ∘ pullbackSwap f (g ∘ pCD)
  middle = Second.flatten ∘ pullbackSwap pCD pCB
  last = Change.forward ∘ Swap.pullbackMap

  associator : MAP (Pullback f (g ∘ pCD)) (Pullback (f ∘ pBC) h)
  associator = last ∘ (middle ∘ first)

  associator-isEquiv : IsEquiv associator
  associator-isEquiv = equiv-compose (middle ∘ first) last
    (equiv-compose first middle
      (equiv-compose (pullbackSwap f (g ∘ pCD)) First.insert
        (pullbackSwap-isEquiv f (g ∘ pCD)) First.insert-isEquiv)
      (equiv-compose (pullbackSwap pCD pCB) Second.flatten
        (pullbackSwap-isEquiv pCD pCB) Second.flatten-isEquiv))
    (equiv-compose Swap.pullbackMap Change.forward SwapEquiv.pullbackMap-isEquiv Change.forward-isEquiv)
```
