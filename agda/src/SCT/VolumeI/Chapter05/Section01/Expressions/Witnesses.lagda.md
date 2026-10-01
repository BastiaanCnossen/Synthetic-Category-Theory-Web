# Normalizing witnesses between expressions

The comparisons of two identification expressions adjust the boundaries of a witness between them. Preservation is then a condition comparing that normalized source witness with the selected target witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors
open import SCT.VolumeI.Chapter05.Section01.Expressions.Identifications
import SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationComparison as Comparison
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WitnessNormalization as WitnessNormalization
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WitnessAction as WitnessAction

module SCT.VolumeI.Chapter05.Section01.Expressions.Witnesses {l : Level} {G : Signature l} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) (I : Interpretation G S)
  {a b : Signature.Object G} {X Y : Syntax.Fun G a b} (s t : Cells.Iso G X Y) where
private
  module S = View S
  module T = View T
  module A = Interpret I
  module B = Interpret (image W I)
  module C = Comparison W K I using (adjust; normalized)
  module N = WitnessNormalization W (A.evaluate-cell s) (A.evaluate-cell t) (C.adjust X Y)
    (B.evaluate-cell s) (B.evaluate-cell t) (C.normalized s) (C.normalized t)
    using (witness-map; normalized; evaluation)

opaque
  action : T.MAP (Weakening.cat W (S._＝_ (A.evaluate-cell s) (A.evaluate-cell t)))
    (T._＝_ (B.evaluate-cell s) (B.evaluate-cell t))
  action = N.witness-map

  normalize : S._=₂_ (A.evaluate-cell s) (A.evaluate-cell t)
    → T._=₂_ (B.evaluate-cell s) (B.evaluate-cell t)
  normalize = N.normalized

  evaluation : (p : S._=₂_ (A.evaluate-cell s) (A.evaluate-cell t))
    → T._=₁_ (WitnessAction.Action.act W action p) (normalize p)
  evaluation = N.evaluation

  expansion : (p : S._=₂_ (A.evaluate-cell s) (A.evaluate-cell t))
    → T._=₃_ (normalize p)
      (T._∙_ (C.normalized t) (T._∙_ (T._◁_ (C.adjust X Y) (Weakening.cell2 W p)) (T._⁻¹ (C.normalized s))))
  expansion p = T.idIso _

-- This is a condition on a specified witness, not a proof of preservation.
Preserves : S._=₂_ (A.evaluate-cell s) (A.evaluate-cell t)
  → T._=₂_ (B.evaluate-cell s) (B.evaluate-cell t) → Set l
Preserves p q = T._=₃_ (normalize p) q
```
