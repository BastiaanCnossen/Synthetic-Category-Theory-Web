# Naturality in a transported witness

The raw naturality square in the composition criterion follows from operation compatibility. The two compatibilities for the selected boundary expressions remain hypotheses.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors
open import SCT.VolumeI.Chapter05.Section01.Expressions.Identifications
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.CoherenceComposition as Closure
import SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationComparison as Comparison
import SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationNormalization as Normalization
import SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationActionComposition as ActionComposition
import SCT.VolumeI.Chapter05.Section01.Expressions.BoundaryComposition as Boundary
import SCT.VolumeI.Chapter05.Section01.Expressions.Witnesses as Witnesses
import SCT.VolumeI.Chapter05.Section01.Expressions.WitnessCompositionCriterion as Criterion
import SCT.VolumeI.Chapter05.Section01.Expressions.NormalizationNaturality as Naturality
import SCT.VolumeI.Chapter05.Section01.Expressions.NaturalitySquares as Squares
import SCT.VolumeI.Chapter05.Section01.Expressions.EndpointTransport as Endpoints

module SCT.VolumeI.Chapter05.Section01.Expressions.WitnessCompositionNaturality {l : Level} {G : Signature l} {R S T : Theory l l l}
  (V : Weakening S T) (W : Weakening R S) (kv : OperationCompatibility V) (kw : OperationCompatibility W)
  (I : Interpretation G R) {a b : Signature.Object G} {X Y : Syntax.Fun G a b}
  (s t : Cells.Iso G X Y) where
private
  module S = View S
  module T = View T
  module R = Interpret I
  kc = Closure.Closure.operations V W kv kw
  module CW = Comparison W kw I
  module NC = Normalization.One (compose V W) I
  module RV = Naturality.One V kv (image W I) X Y
  module RW = Naturality.One W kw I X Y
  module NT = Naturality.Two V W kv kw kc I X Y
  module AC = ActionComposition V W kv I using (point-composes)
  module BC = Boundary V W kv kw I
  module PW = Witnesses W kw I s t using (normalize; expansion)
  module PV = Witnesses V kv (image W I) s t using (normalize)
  module PC = Witnesses (compose V W) kc I s t using (normalize)
  module CR = Criterion V W kv kw I s t

opaque
  raw-naturality : (p : CR.Witness) → CR.RawNaturality p
  raw-naturality p = Squares.paste T
    (AC.point-composes X Y (R.evaluate-cell s)) (RV.raw (CW.normalized s))
    (AC.point-composes X Y (R.evaluate-cell t)) (RV.raw (CW.normalized t))
    (CR.raw-direct p) (RV.raw (RW.raw p)) (CR.raw-successive p)
    (NT.point-composes p)
    (RV.square (CW.normalized s) (CW.normalized t) (RW.raw p) (PW.normalize p)
      (Endpoints.changeEndpoints-to-square S (CW.normalized s) (CW.normalized t)
        (RW.raw p) (PW.normalize p) (S._⁻¹ (PW.expansion p))))

  normalization-composes : BC.Compatible s → BC.Compatible t → (p : CR.Witness)
    → T._=₃_ (PC.normalize p) (PV.normalize (PW.normalize p))
  normalization-composes first second p = CR.normalization-composes first second p (raw-naturality p)

-- The raw naturality hypothesis is now discharged from the existing operation
-- compatibility. Only compatibility of the two CHOSEN boundary recipes remains.
```
