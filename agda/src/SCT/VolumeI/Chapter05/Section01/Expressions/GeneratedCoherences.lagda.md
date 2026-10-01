# The recursive pentagon and triangle comparisons

The general expression interpreter normalizes both coherence witnesses. Preservation of each resulting witness is a separate condition. Agreement with the specialized comparison formulas has not been proved.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors
open import SCT.VolumeI.Chapter05.Section01.Expressions.Identifications
import SCT.VolumeI.Chapter05.Section01.Expressions.CoherenceExpressions as Templates
import SCT.VolumeI.Chapter05.Section01.Expressions.Witnesses as Witnesses

module SCT.VolumeI.Chapter05.Section01.Expressions.GeneratedCoherences {l : Level} {G : Signature l} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) (I : Interpretation G S) where
private
  module S = View S
  module T = View T
  module A = Evaluate I
  module B = Evaluate (image W I)
  module AT = Interpret I
  module BT = Interpret (image W I)
open Signature G
open Syntax G

module Pentagon {a b c d e : Object} (f : Fun a b) (g : Fun b c) (h : Fun c d) (k : Fun d e) where
  private
    module P = Templates.Pentagon G f g h k
  module N = Witnesses W K I P.short P.long using (action; normalize; evaluation; expansion; Preserves)
  source : S._=₂_ (AT.evaluate-cell P.short) (AT.evaluate-cell P.long)
  source = S.comp-pentagon (A.evaluate f) (A.evaluate g) (A.evaluate h) (A.evaluate k)
  target : T._=₂_ (BT.evaluate-cell P.short) (BT.evaluate-cell P.long)
  target = T.comp-pentagon (B.evaluate f) (B.evaluate g) (B.evaluate h) (B.evaluate k)
  transported : T._=₂_ (BT.evaluate-cell P.short) (BT.evaluate-cell P.long)
  transported = N.normalize source
  Preservation : Set l
  Preservation = N.Preserves source target

module Triangle {a b c : Object} (f : Fun a b) (g : Fun b c) where
  private
    module P = Templates.Triangle G f g
  module N = Witnesses W K I P.short P.long using (action; normalize; evaluation; expansion; Preserves)
  source : S._=₂_ (AT.evaluate-cell P.short) (AT.evaluate-cell P.long)
  source = S.comp-triangle (A.evaluate f) (A.evaluate g)
  target : T._=₂_ (BT.evaluate-cell P.short) (BT.evaluate-cell P.long)
  target = T.comp-triangle (B.evaluate f) (B.evaluate g)
  transported : T._=₂_ (BT.evaluate-cell P.short) (BT.evaluate-cell P.long)
  transported = N.normalize source
  Preservation : Set l
  Preservation = N.Preserves source target

-- No specialized pentagon or triangle boundary proof is imported. The same
-- recursive expression comparison supplies both. Agreement with the earlier
-- hand-built normalization recipes is a separate, unproved comparison.
```
