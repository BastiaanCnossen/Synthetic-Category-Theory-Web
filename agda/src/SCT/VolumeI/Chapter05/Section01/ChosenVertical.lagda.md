# The selected vertical-composition laws

The comparisons below preserve the chosen units, inverses, and associativity for vertical composition. Their boundaries are the parameterized comparisons constructed in VerticalBoundary.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.ChosenVertical where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.VerticalBoundary as Boundary

record ChosenVertical {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) : Set l where
  private
    module S = View S
    module T = View T
    module B = Boundary W K
  open Weakening W using (phi)
  field
    left-unit : {C D : S.CAT} (f g : S.MAP C D)
      → B.Unary.Left.Preserves f g (S.isoComp-unitˡ f g) (Calculus.unitˡ T (phi f g))
    right-unit : {C D : S.CAT} (f g : S.MAP C D)
      → B.Unary.Right.Preserves f g (S.isoComp-unitʳ f g) (Calculus.unitʳ T (phi f g))
    left-inverse : {C D : S.CAT} (f g : S.MAP C D)
      → B.Unary.InverseLeft.Preserves f g (S.isoComp-inverseˡ f g) (B.Unary.target-inverse-left f g)
    right-inverse : {C D : S.CAT} (f g : S.MAP C D)
      → B.Unary.InverseRight.Preserves f g (S.isoComp-inverseʳ f g) (B.Unary.target-inverse-right f g)
    associativity : {C D : S.CAT} (f g h k : S.MAP C D)
      → B.Associativity.Law.Preserves f g h k (S.isoComp-assoc f g h k) (B.Associativity.target f g h k)
```
