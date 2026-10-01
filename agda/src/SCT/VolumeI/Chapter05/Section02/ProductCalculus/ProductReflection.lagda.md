# The computation rule for reflection

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
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.CurryingLifting as Lifting

module SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductReflection
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Products.DependentProducts P
open Action W P using (reflect)
open T using (_∘_; _◁_; _▷_; _⁻¹)

action : {X : S.CAT} {B : T.CAT} {h k : S.MAP X (Π B)}
  → S._=₁_ h k → T._=₁_ (uncurry h) (uncurry k)
action {h = h} {k} α = (uncurry-family h k ∘ W.map α) ∘ W.back

reflect-β : {X : S.CAT} {B : T.CAT} {h k : S.MAP X (Π B)}
  (α : T._=₁_ (uncurry h) (uncurry k)) → T._=₂_ (action (reflect α)) α
reflect-β {h = h} {k} α =
  Lifting.Along.point-β W P (uncurry-family h k) (comparison-isEquiv h k) α

module Families {X : S.CAT} {B : T.CAT} (h k : S.MAP X (Π B)) where
  open Lifting.Along W P (uncurry-family h k) (comparison-isEquiv h k)
    public using () renaming (lift to reflect-family; lift-β to reflect-family-β)
```
