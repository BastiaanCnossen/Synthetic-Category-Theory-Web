# Total recovery as an equivalence over the base

The constructed triangle for total recovery is retained when its inverse
is formed. This applies the relative inverse theorem from Chapter 3 to
the underlying equivalence in the recovery axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackData as PullbackData
import SCT.VolumeI.Chapter03.RelativeCategories.Equivalences as Relative
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section03.GenericFiber as Fiber
import SCT.VolumeI.Chapter05.Section03.Recovery as Recovery

module SCT.VolumeI.Chapter05.Section03.RecoveryOverBase
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (MS : Mapping.MappingAnimae S) (FS : Functors.FunctorCategories S MS)
  (PS : Pullbacks.PullbackStructure S)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (PT : PullbackData.PullbackData T) (R : Recovery.Recovery W P Q A e PT) where

private
  module S = View S
module F = Fiber W P Q A e PT using (total-recovery-functor)
module R = Recovery.Recovery R

module Over {X : S.CAT} (p : S.MAP X (S.AN.category A)) where
  open Relative.Inverse S MS FS PS (F.total-recovery-functor p) (R.total-isEquiv p)
    public using (inverse; left-inverse; right-inverse)
```
