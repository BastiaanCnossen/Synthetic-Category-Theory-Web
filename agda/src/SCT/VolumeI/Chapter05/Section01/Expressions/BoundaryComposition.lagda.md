# Compatibility of selected boundary comparisons

The direct and successive comparisons of an identification expression need an identification at the next level. Compatible states this precise remaining obligation; it does not supply or postulate an inhabitant.

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

module SCT.VolumeI.Chapter05.Section01.Expressions.BoundaryComposition {l : Level} {G : Signature l} {R S T : Theory l l l}
  (V : Weakening S T) (W : Weakening R S) (kv : OperationCompatibility V) (kw : OperationCompatibility W)
  (I : Interpretation G R) where
private
  module T = View T
  module R = Interpret I
  module U = Interpret (image V (image W I))
  module V = Weakening V
  module CW = Comparison W kw I
  module CV = Comparison V kv (image W I)
  module CC = Comparison (compose V W) (Closure.Closure.operations V W kv kw) I
  module NC = Normalization.One (compose V W) I
  module NV = Normalization.One V (image W I)
  module AC = ActionComposition V W kv I using (point-composes)
open Signature G
open Syntax G renaming (compose to composite)
open Cells G
open T using (_∙_; _◁_)

bridge : {a b : Object} {X Y : Fun a b} (s : Iso X Y)
  → T._=₂_ (NC.normalize X Y (R.evaluate-cell s)) (NV.normalize X Y (Interpret.evaluate-cell (image W I) s))
bridge {X = X} {Y} s = (NV.adjust X Y ◁ V.cell2 (CW.normalized s)) ∙
  AC.point-composes X Y (R.evaluate-cell s)

opaque
  successive : {a b : Object} {X Y : Fun a b} (s : Iso X Y)
    → T._=₂_ (NC.normalize X Y (R.evaluate-cell s)) (U.evaluate-cell s)
  successive s = CV.normalized s ∙ bridge s

Compatible : {a b : Object} {X Y : Fun a b} → Iso X Y → Set l
Compatible s = T._=₃_ (CC.normalized s) (successive s)

-- This is the precise comparison of the recursively CHOSEN boundary
-- witnesses that remains to be proved. For a pentagon, instantiate it at
-- both its short and long identification expressions. The family action
-- comparison used in successive is proved, not an extra hypothesis.
-- No inhabitant of Compatible is postulated by this module.
```
