# The selected pentagon and triangle

After their boundary identifications have been transported, the source pentagon and triangle are compared with the selected target witnesses. These comparisons are primitive data; operation compatibility alone does not identify the selected witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.ChosenCoherences where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.PentagonBoundary as PentagonBoundary
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.TriangleBoundary as TriangleBoundary

-- Required data, not a conjectured consequence of operation compatibility.
-- The current canonical Theory has one specified composition triangle.
record ChosenCoherences {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) : Set l where
  private
    module S = View S
    module T = View T
    module W = Weakening W
  field
    pentagon : {A B C D E : S.CAT} (f : S.MAP A B) (g : S.MAP B C)
      (h : S.MAP C D) (k : S.MAP D E)
      → T._=₃_ (PentagonBoundary.transported-pentagon W K f g h k)
        (T.comp-pentagon (W.map f) (W.map g) (W.map h) (W.map k))
    triangle : {C D E : S.CAT} (f : S.MAP C D) (g : S.MAP D E)
      → T._=₃_ (TriangleBoundary.transported-triangle W K f g)
        (T.comp-triangle (W.map f) (W.map g))

record ChosenWeakening {l : Level} (S T : Theory l l l) : Set l where
  field
    weakening : Weakening S T
    operations : OperationCompatibility weakening
    chosen : ChosenCoherences weakening operations

-- This bundle does not yet assert preservation of every primitive witness of
-- Theory. PrimitivePreservation assembles the remaining witness families.
```
