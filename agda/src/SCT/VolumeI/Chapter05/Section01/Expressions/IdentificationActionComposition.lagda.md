# Composition on identification animae

The direct and successive actions are compared as functors on the whole weakened identification anima. Evaluation gives the corresponding comparison for an arbitrary identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors
import SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationNormalization as Normalization
import SCT.VolumeI.Chapter05.Section01.Expressions.FunctorComposition as FunctorComposition
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WitnessAction as Action

module SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationActionComposition {l : Level} {G : Signature l} {R S T : Theory l l l}
  (V : Weakening S T) (W : Weakening R S) (kv : OperationCompatibility V) (I : Interpretation G R) where
private
  module T = View T
  module E = Evaluate I
  module ES = Evaluate (image W I)
  module A = Compare W I
  module B = Compare V (image W I)
  module C = Compare (compose V W) I
  module NW = Normalization.One W I
  module NV = Normalization.One V (image W I)
  module NC = Normalization.One (compose V W) I
  module V = Weakening V
  module W = Weakening W
  module FC = FunctorComposition V W kv I using (comparison-composes)
open Signature G
open Syntax G renaming (compose to composite)
open T using (_∘_; _∙_; _⁻¹)
open Calculus T

module Pair {a b : Object} (X Y : Fun a b) where
  raw = Operations.family V (W.phi (E.evaluate X) (E.evaluate Y))
  middle = Operations.family V (NW.action X Y)
  final = NV.adjust X Y ∘ middle

  opaque
    first-square : T._=₁_ (T.const (V.term (A.comparison Y)) ∙ raw)
      (middle ∙ T.const (V.term (A.comparison X)))
    first-square = Operations.transport-square V kv (A.comparison X) (A.comparison Y)
      (W.phi (E.evaluate X) (E.evaluate Y)) (NW.action X Y) (NW.family-square X Y)

    second-square : T._=₁_ (T.const (B.comparison Y) ∙ middle) (final ∙ T.const (B.comparison X))
    second-square = Squares.unsolve T (B.comparison X) (B.comparison Y) middle final (T.idIso _)

    composite-square : T._=₁_ (T.const (C.comparison Y) ∙ raw) (final ∙ T.const (C.comparison X))
    composite-square = isoComp-cong (const-cong (FC.comparison-composes Y)) (T.idIso _) then
      Squares.paste T (V.term (A.comparison X)) (B.comparison X)
        (V.term (A.comparison Y)) (B.comparison Y) raw middle final first-square second-square then
      isoComp-cong (T.idIso _) (const-cong ((FC.comparison-composes X) ⁻¹))

    action-composes : T._=₁_ (NC.action X Y) (NV.action X Y ∘ V.map (NW.action X Y))
    action-composes = Squares.solve T (C.comparison X) (C.comparison Y) raw final composite-square then
      (T.comp-assoc (V.map (NW.action X Y)) (V.phi (ES.evaluate X) (ES.evaluate Y)) (NV.adjust X Y)) ⁻¹

-- This is an identification of functors on the WHOLE weakened identification
-- anima. It is stronger than a family of unrelated pointwise witnesses.
action-composes : {a b : Object} (X Y : Fun a b)
  → T._=₁_ (NC.action X Y) (NV.action X Y ∘ V.map (NW.action X Y))
action-composes X Y = Pair.action-composes X Y

opaque
  -- Choose the point comparison by evaluating the FAMILY comparison above.
  -- Its equality with the separately constructed point proof in
  -- IdentificationNormalization.Two is not assumed or needed here.
  point-composes : {a b : Object} (X Y : Fun a b)
    (alpha : View._=₁_ R (E.evaluate X) (E.evaluate Y))
    → T._=₂_ (NC.normalize X Y alpha) (NV.normalize X Y (NW.normalize X Y alpha))
  point-composes X Y alpha = (NC.evaluation X Y alpha) ⁻¹ then
    Action.Two.compare-action V W (NW.action X Y) (NV.action X Y) (NC.action X Y)
      alpha _ (action-composes X Y)
      (Action.Two.preserves V W (NW.action X Y) (NV.action X Y)
        alpha (NW.normalize X Y alpha) (NV.normalize X Y (NW.normalize X Y alpha))
        (NW.evaluation X Y alpha) (NV.evaluation X Y (NW.normalize X Y alpha)))
```
