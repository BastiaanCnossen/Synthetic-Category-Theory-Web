# Dependent products preserve pullbacks

The dependent product of a pullback cone is a pullback cone. Its legs
are the dependent products of the original legs; its matching is obtained
by currying the whole cone. The restriction condition in the lifting
criterion is supplied by the comparison with the evaluation cospan.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductConeRestriction as Restriction
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductPullbackCriterion as Criterion
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter05.Section02.ProductPullbacks
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W)
  (PS : Pullbacks.PullbackStructure S) (PT : Pullbacks.PullbackStructure T) where

open Criterion W K P PS PT using (module TS)

module Preservation {B C D Z : View.CAT T}
  {f : View.MAP T B D} {g : View.MAP T C D}
  (s : TS.Cone f g Z) (universal : TS.IsPullback s) =
  Criterion.FromRestriction W K P PS PT (Restriction.restrict W K P PT) s universal
```
