# Reflection for dependent sums

Reflection of an identification is more than existence of a lift. The
lift constructed from the inverse comparison actually evaluates to the
given local identification. This calculation retains the terminal
comparison in weakening and the chosen retraction of the identification
comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.CurryingLifting as Lifting

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumReflection
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Sums.DependentSums Q
open Action W P Q using (reflect)
open T using (_∘_; _◁_; _▷_; _⁻¹)

action : {B : T.CAT} {D : S.CAT} {h k : S.MAP (Σ B) D}
  → S._=₁_ h k → T._=₁_ (flatten h) (flatten k)
action {h = h} {k} α = (flatten-family h k ∘ W.map α) ∘ W.back

reflect-β : {B : T.CAT} {D : S.CAT} {h k : S.MAP (Σ B) D}
  (α : T._=₁_ (flatten h) (flatten k)) → T._=₂_ (action (reflect α)) α
reflect-β {h = h} {k} α =
  Lifting.Along.point-β W P (flatten-family h k) (comparison-isEquiv h k) α

module Families {B : T.CAT} {D : S.CAT} (h k : S.MAP (Σ B) D) where
  open Lifting.Along W P (flatten-family h k) (comparison-isEquiv h k)
    public using () renaming (lift to reflect-family; lift-β to reflect-family-β)
```
