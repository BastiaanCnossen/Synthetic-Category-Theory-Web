# A criterion for successive witness normalization

Successive second-level normalization follows from compatibility of its two selected boundary comparisons and a raw naturality square. The theorem retains these inputs explicitly.

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
import SCT.VolumeI.Chapter05.Section01.Expressions.BoundaryComposition as Boundary
import SCT.VolumeI.Chapter05.Section01.Expressions.Witnesses as Witnesses
import SCT.VolumeI.Chapter05.Section01.Expressions.NormalizationPasting as Pasting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section01.Expressions.WitnessCompositionCriterion {l : Level} {G : Signature l} {R S T : Theory l l l}
  (V : Weakening S T) (W : Weakening R S) (kv : OperationCompatibility V) (kw : OperationCompatibility W)
  (I : Interpretation G R) {a b : Signature.Object G} {X Y : Syntax.Fun G a b}
  (s t : Cells.Iso G X Y) where
private
  module T = View T
  module R = Interpret I
  module V = Weakening V
  module VW = Weakening (compose V W)
  kc = Closure.Closure.operations V W kv kw
  module BC = Boundary V W kv kw I
  module CC = Comparison (compose V W) kc I
  module CV = Comparison V kv (image W I)
  module NC = Normalization.One (compose V W) I
  module NV = Normalization.One V (image W I)
  module PW = Witnesses W kw I s t using (normalize)
  module PV = Witnesses V kv (image W I) s t using (normalize; expansion)
  module PC = Witnesses (compose V W) kc I s t using (normalize; expansion)
open T using (_∙_; _◁_; _⁻¹)
open Calculus T using (_then_)

Witness = View._=₂_ R (R.evaluate-cell s) (R.evaluate-cell t)

raw-direct : (p : Witness) → T._=₂_ (NC.normalize X Y (R.evaluate-cell s)) (NC.normalize X Y (R.evaluate-cell t))
raw-direct p = NC.adjust X Y ◁ VW.cell2 p

raw-successive : (p : Witness)
  → T._=₂_ (NV.normalize X Y (Interpret.evaluate-cell (image W I) s))
    (NV.normalize X Y (Interpret.evaluate-cell (image W I) t))
raw-successive p = NV.adjust X Y ◁ V.cell2 (PW.normalize p)

-- Naturality of the comparison bridge with respect to p. It does not compare
-- the final chosen target witness and is not silently assumed by the theorem.
RawNaturality : Witness → Set l
RawNaturality p = T._=₃_ (BC.bridge t ∙ raw-direct p) (raw-successive p ∙ BC.bridge s)

opaque
  unfolding BC.successive
  normalization-composes : BC.Compatible s → BC.Compatible t
    → (p : Witness) → RawNaturality p
    → T._=₃_ (PC.normalize p) (PV.normalize (PW.normalize p))
  normalization-composes first second p naturality = PC.expansion p then
    Pasting.compare T (raw-direct p) (raw-successive p) (BC.bridge s) (BC.bridge t)
      (CC.normalized s) (CC.normalized t) (CV.normalized s) (CV.normalized t)
      naturality first second then (PV.expansion (PW.normalize p)) ⁻¹

-- This is a proved reduction of the requested higher composition theorem to
-- two boundary-comparison compatibilities and one raw naturality square.
-- None of these three inputs is postulated here. The later module
-- WitnessCompositionNaturality proves the raw naturality input from the
-- existing operation compatibility, leaving only the two boundary inputs.
```
