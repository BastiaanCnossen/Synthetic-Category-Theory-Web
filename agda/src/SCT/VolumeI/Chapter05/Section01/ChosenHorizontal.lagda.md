# The selected horizontal-composition laws

Horizontal units, associativity, and the fixed-input interchange laws are compared using the normalized boundaries. No joint interchange assumption is introduced.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.ChosenHorizontal where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.HorizontalBoundary as Boundary

record ChosenHorizontal {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) : Set l where
  private
    module S = View S
    module B = Boundary W K
  field
    left-unit : {C D : S.CAT} (f g : S.MAP C D)
      → B.LeftUnit.Law.Preserves f g (S.hcomp-unitˡ f g) (B.LeftUnit.target f g)
    right-unit : {C D : S.CAT} (f g : S.MAP C D)
      → B.RightUnit.Law.Preserves f g (S.hcomp-unitʳ f g) (B.RightUnit.target f g)
    associativity : {B C D E : S.CAT} (f f' : S.MAP B C) (g g' : S.MAP C D) (h h' : S.MAP D E)
      → B.Associativity.Law.Preserves f f' g g' h h'
        (S.hcomp-assoc f f' g g' h h') (B.Associativity.target f f' g g' h h')
```
