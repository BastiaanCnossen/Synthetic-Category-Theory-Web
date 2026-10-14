# Associativity over a common base

The three stages retain the chosen nesting, symmetry and boundary-change
comparisons. They construct the equivalence between the two parenthesized
pullbacks of three arrows to the common base. No higher associator coherence
is inferred from these chosen operations.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.PullbackAssociativity where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (id-isEquiv; equiv-compose)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeTransport using (cone-swap)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctoriality
open import SCT.VolumeI.Chapter01.Section06.NestedPullbacks using (module ChosenNested)

module _ {Γ : Context} where
  module Associativity {B C D E : CAT Γ} (f : MAP B E) (g : MAP C E) (h : MAP D E) where
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
    module First = ChosenNested pCD g f
    module Second = ChosenNested pCB g h

    swap-cospan : CospanMap (g ∘ pCB) h (g ∘ qBC) h
    swap-cospan = record
      { left = pullback-swap g f; right = id D; base = id E
      ; left-square = (comp-unitˡ (g ∘ pCB)) ⁻¹ ∙
          ((g ◁ pullback-factor-β₂ (cone-swap (pullback-cone g f))) ∙
            comp-assoc (pullback-swap g f) qBC g)
      ; right-square = (comp-unitˡ h) ⁻¹ ∙ comp-unitʳ h }
    module Swap = CospanEquivalence swap-cospan (pullback-swap-isEquiv g f)
      (id-isEquiv D) (id-isEquiv E)
    module Change = ChangeLeftArrow ((pullback-match {f = f} {g}) ⁻¹) h

    first : MAP (Pullback f (g ∘ pCD)) (Pullback pCD pCB)
    first = First.insert ∘ pullback-swap f (g ∘ pCD)
    middle : MAP (Pullback pCD pCB) (Pullback (g ∘ pCB) h)
    middle = Second.flatten ∘ pullback-swap pCD pCB
    last : MAP (Pullback (g ∘ pCB) h) (Pullback (f ∘ pBC) h)
    last = Change.forward ∘ pullback-map swap-cospan

    associator : MAP (Pullback f (g ∘ pCD)) (Pullback (f ∘ pBC) h)
    associator = last ∘ (middle ∘ first)

    associator-isEquiv : IsEquiv associator
    associator-isEquiv = equiv-compose (middle ∘ first) last
      (equiv-compose first middle
        (equiv-compose (pullback-swap f (g ∘ pCD)) First.insert
          (pullback-swap-isEquiv f (g ∘ pCD)) First.insert-isEquiv)
        (equiv-compose (pullback-swap pCD pCB) Second.flatten
          (pullback-swap-isEquiv pCD pCB) Second.flatten-isEquiv))
      (equiv-compose (pullback-map swap-cospan) Change.forward Swap.pullback-map-isEquiv Change.forward-isEquiv)
```
