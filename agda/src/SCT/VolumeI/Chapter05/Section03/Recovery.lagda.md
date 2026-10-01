# The recovery axiom

The axiom applies to the maps already constructed in `GenericFiber`.
For total recovery we record that its underlying functor is an
equivalence. Its specified triangle is `total-recovery-over`; the
relative inverse theorem supplies the inverse and both identifications
over the base from these data.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section03.GenericFiber as Fiber
import SCT.VolumeI.Chapter01.Section06.PullbackData as Pullbacks

module SCT.VolumeI.Chapter05.Section03.Recovery
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (R : Pullbacks.PullbackData T) where

private
  module S = View S
  module T = View T
open Fiber W P Q A e R using (local-recovery; total-recovery)

record Recovery : Set l where
  field
    local-isEquiv : (B : T.CAT) → T.IsEquiv (local-recovery B)
    total-isEquiv : {X : S.CAT} (p : S.MAP X (S.AN.category A)) → S.IsEquiv (total-recovery p)
```
