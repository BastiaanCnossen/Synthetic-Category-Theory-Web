# Fibers of a pullback projection

For a pullback of f and g, base change of its second projection along y
is equivalent to the pullback of f along g y. A specified identification
g y = z then gives the pullback along z.

The parameter category of y is arbitrary. The comparison uses the actual
swapped pullback cone, its nested-pullback flattening, and the chosen arrow
change. These maps remain transparent; their full cone laws belong to the
three existing constructions. No matching is replaced by an identity.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.ProjectionFibers where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (IsContractible)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-compose; equiv-inverse; contractible-source)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
  using (Pullback; pullback₂; pullback-cone)
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions
  using (pullback-swap; pullback-swap-isEquiv; pullback-cone-isPullback; pullback₂-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.ConeTransport using (cone-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality using (module SwappedCone)
open import SCT.VolumeI.Chapter01.Section06.NestedPullbacks using (module Nested)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange using (module ChangeLeftArrow)

module FiberComparison {Γ : Context} {A B C T : CAT Γ}
  (f : MAP A C) (g : MAP B C) (y : MAP T B) (z : MAP T C)
  (α : (g ∘ y) =₁ z) where

  base : MAP (Pullback f g) B
  base = pullback₂

  private
    module N = Nested y g f (cone-swap (pullback-cone f g))
      (SwappedCone.isPullback (pullback-cone f g) (pullback-cone-isPullback f g))
    module Change = ChangeLeftArrow α f

    nested-to-target : MAP (Pullback y base) (Pullback f z)
    nested-to-target = pullback-swap z f ∘ (Change.forward ∘ N.flatten)

    nested-to-target-isEquiv : IsEquiv nested-to-target
    nested-to-target-isEquiv = equiv-compose (Change.forward ∘ N.flatten) (pullback-swap z f)
      (equiv-compose N.flatten Change.forward N.flatten-isEquiv Change.forward-isEquiv)
      (pullback-swap-isEquiv z f)

  fiber-to-target : MAP (Pullback base y) (Pullback f z)
  fiber-to-target = nested-to-target ∘ pullback-swap base y

  fiber-to-target-isEquiv : IsEquiv fiber-to-target
  fiber-to-target-isEquiv = equiv-compose (pullback-swap base y) nested-to-target
    (pullback-swap-isEquiv base y) nested-to-target-isEquiv

  target-contractible : IsEquiv base → IsContractible T → IsContractible (Pullback f z)
  target-contractible e t = contractible-source (IsEquiv.inverse fiber-to-target-isEquiv)
    (equiv-inverse fiber-to-target-isEquiv)
    (contractible-source (pullback₂ {f = base} {g = y}) (pullback₂-isEquiv base y e) t)
```
