# Associativity over a common base

For maps from `B`, `C`, and `D` to `E`, the module `PullbackAssociativity`
constructs `associator` from `B ×_E (C ×_E D)` to `(B ×_E C) ×_E D` and
proves `associator-isEquiv`.

The construction combines two nested-pullback comparisons with symmetry.
The final boundary change uses the specified matching of the first two
factors, so the map to the common base goes through the first projection
on both sides. The local names `first`, `middle`, and `last` are the three
successive factors of the displayed associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.PullbackAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Pasting.NestedPullbacks 𝒯 P using (module Nested)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P using (module CospanEquivalence)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)

```

## The intermediate pullbacks

We use the nested-pullback equivalence twice. `CD`, `CB`, and `BC` name the
three binary pullbacks over the common base; their projections determine
the cospans used in the intermediate steps.

```agda
module PullbackAssociativity {B C D E : CAT} (f : MAP B E) (g : MAP C E) (h : MAP D E) where

  CD = Pullback g h
  CB = Pullback g f
  BC = Pullback f g
  pCD : MAP CD C
  pCD = pullback₁
  pCB : MAP CB C
  pCB = pullback₁
  pBC : MAP BC B
  pBC = pullback₁
  qBC : MAP BC C
  qBC = pullback₂
  module First = Nested pCD g f
  module Second = Nested pCB g h

```

## Comparing the maps to the base

Swapping `CB` to `BC` transports the intermediate cospan. Its map to the
base initially uses the `C` projection. The matching of `BC` identifies
this with the map through `B`; `Change` makes that final adjustment.

```agda
  swapCospan : CospanMap (g ∘ pCB) h (g ∘ qBC) h
  swapCospan = record
    { left = pullbackSwap g f ; right = id D ; base = id E
    ; leftSquare = (comp-unitˡ (g ∘ pCB)) ⁻¹ ∙
        ((g ◁ pullbackLift-β₂ (coneSwap (pullbackCone g f))) ∙ comp-assoc (pullbackSwap g f) qBC g)
    ; rightSquare = (comp-unitˡ h) ⁻¹ ∙ comp-unitʳ h }
  module Swap = CospanMap swapCospan
  module SwapEquiv = CospanEquivalence swapCospan (pullbackSwap-isEquiv g f) (id-isEquiv D) (id-isEquiv E)
    using (pullbackMap-isEquiv)
  module Change = ChangeLeft ((pullbackMatch {f = f} {g}) ⁻¹) h

```

## Composing the equivalences

`first` and `middle` use the two nested-pullback equivalences and symmetry.
`last` performs the cospan comparison and the adjustment just described.
Their composite is the desired associator, and each factor is an equivalence.

```agda
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
