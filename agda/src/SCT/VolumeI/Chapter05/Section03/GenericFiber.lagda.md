# Generic fibers and the recovery maps

The local pullback at the generic point defines the generic fiber of a
category over the base. Both recovery maps are constructed before the
axiom asserting that they are equivalences. In particular, the total
recovery map carries a constructed identification with the base projection.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as Action
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point
import SCT.VolumeI.Chapter01.Section06.PullbackData as Pullbacks
import SCT.VolumeI.Chapter01.Section06.Cones as Cones
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section03.GenericFiber
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (R : Pullbacks.PullbackData T) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Sums.DependentSums Q
open Action W P Q using (reflect; flatten-post)
open Point W P Q A e using (base; generic; projection; projection-β)
open Pullbacks.PullbackData R
open Cones T using (Cone)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

Fiber : {X : S.CAT} → S.MAP X base → T.CAT
Fiber p = Pullback generic (W.map p)

fiber-inclusion : {X : S.CAT} (p : S.MAP X base) → T.MAP (Fiber p) (W.cat X)
fiber-inclusion p = pullback₂

recovery-cone : (B : T.CAT) → Cone generic (W.map (projection B)) B
recovery-cone B = record
  { left = T.terminate B ; right = pair B ; match = (projection-β B) ⁻¹ }

local-recovery : (B : T.CAT) → T.MAP B (Fiber (projection B))
local-recovery B = pullbackLift (recovery-cone B)

local-recovery-β : (B : T.CAT)
  → T._=₁_ (fiber-inclusion (projection B) ∘ local-recovery B) (pair B)
local-recovery-β B = pullbackLift-β₂ (recovery-cone B)

total-recovery : {X : S.CAT} (p : S.MAP X base) → S.MAP (Σ (Fiber p)) X
total-recovery p = extend (fiber-inclusion p)

total-recovery-over : {X : S.CAT} (p : S.MAP X base)
  → S._=₁_ (S._∘_ p (total-recovery p)) (projection (Fiber p))
total-recovery-over p = reflect
  (flatten-post p (total-recovery p) then
    (W.map p ◁ (extend-β (fiber-inclusion p)) ⁻¹) then
    pullbackMatch ⁻¹ then (generic ◁ T.terminal-iso _ _) then
    (projection-β (Fiber p)) ⁻¹)

total-recovery-functor : {X : S.CAT} (p : S.MAP X base)
  → S.FunctorLift p (projection (Fiber p))
total-recovery-functor p = record
  { lift = total-recovery p ; comparison = total-recovery-over p }

fiber-isAn : {X : S.CAT} (p : S.MAP X base) → S.isAn X → T.isAn (Fiber p)
fiber-isAn p xAn = pullback-isAn generic (W.map p)
  T.one-isAn (W.anima xAn) (W.anima (S.AN.witness A))
```
