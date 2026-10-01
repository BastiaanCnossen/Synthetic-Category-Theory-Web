# The selected terminal universal property

For two functors to the terminal category, the terminal axiom supplies
a selected equivalence from their identification anima to the terminal
category. We weaken the source category and compose each weakened functor
with the terminal comparison. The universal-property functor comparison is
obtained by applying the existing
comparison operations for identification animae and terminal maps.
There is no independently supplied comparison square here.

Preservation of the selected equivalence compares its inverse, section,
and retraction. In particular, its inverse comparison is precisely the
comparison of the terminal identification constructed from that inverse.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Products using (PreservesProducts)
import SCT.VolumeI.Chapter05.Section01.Expressions.ComparisonObjects as Objects
import SCT.VolumeI.Chapter05.Section01.ComparisonWitnesses as Witnesses

module SCT.VolumeI.Chapter05.Section01.TerminalPreservation
  {l : Level} {S T : Theory l l l} (W : Weakening S T) (P : PreservesProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
module O = Objects W P
module E = Witnesses W P

fixed : S.CAT → O.Object
fixed C = record { source = C ; target = W.cat C
  ; comparison = record { functor = T.id (W.cat C) ; isEquiv = T.id-isEquiv (W.cat C) } }

to-terminal : {C : S.CAT} → S.MAP C S.One → O.Arrow (fixed C) O.one
to-terminal f = record { source = f ; target = T._∘_ (O.Object.arrow O.one) (W.map f)
  ; square = T._⁻¹ (T.comp-unitʳ _) }

record Comparison : Set l where
  field
    universal : {C : S.CAT} (f g : S.MAP C S.One)
      → E.EquivalenceComparison (O.terminate (O.identifications (to-terminal f) (to-terminal g)))
          (S.terminalIso-isEquiv f g)
          (T.terminalIso-isEquiv (O.Arrow.target (to-terminal f)) (O.Arrow.target (to-terminal g)))

  identification : {C : S.CAT} (f g : S.MAP C S.One)
    → E.CellComparison (to-terminal f) (to-terminal g)
        (S.terminal-iso f g)
        (T.terminal-iso (O.Arrow.target (to-terminal f)) (O.Arrow.target (to-terminal g)))
  identification f g = E.EquivalenceComparison.inverse (universal f g)
```
