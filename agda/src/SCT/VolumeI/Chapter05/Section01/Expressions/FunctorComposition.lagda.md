# Composition of functor-expression comparisons

Structural induction compares the direct expression comparison for a composite change with the successive comparison. No separate hypothesis is assumed for a complete expression.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors
import SCT.VolumeI.Chapter05.Section01.Expressions.TermCalculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations

module SCT.VolumeI.Chapter05.Section01.Expressions.FunctorComposition {l : Level} {G : Signature l}
  {R S T : Theory l l l} (V : Weakening S T) (W : Weakening R S)
  (kv : OperationCompatibility V) (I : Interpretation G R) where
private
  module T = View T
  module R = Evaluate I
  module S = Evaluate (image W I)
  module V = Weakening V
  module W = Weakening W
  module A = Compare W I
  module B = Compare V (image W I)
  module C = Compare (compose V W) I
open Signature G
open Syntax G renaming (compose to composite)
open T using (_∙_; _⋆_; _⁻¹)
open Calculus.Local T

opaque
  composition-case : {a b c : Object} (Y : Fun b c) (X : Fun a b)
    → T._=₂_ (C.comparison Y) (B.comparison Y ∙ V.term (A.comparison Y))
    → T._=₂_ (C.comparison X) (B.comparison X ∙ V.term (A.comparison X))
    → T._=₂_ (C.comparison (composite Y X))
      (B.comparison (composite Y X) ∙ V.term (A.comparison (composite Y X)))
  composition-case Y X ky kx =
    isoComp-cong (hcomp-cong ky kx then
      hcomp-isoComp (B.comparison Y) (V.term (A.comparison Y)) (B.comparison X) (V.term (A.comparison X)))
      (T.idIso _) then
    reassociateFour (B.comparison Y ⋆ B.comparison X)
      (V.term (A.comparison Y) ⋆ V.term (A.comparison X))
      (V.comp (W.map (R.evaluate X)) (W.map (R.evaluate Y))) (V.term (W.comp (R.evaluate X) (R.evaluate Y))) then
    isoComp-cong (T.idIso _)
      (isoComp-cong ((Calculus.Transport.horizontal-term V kv (A.comparison Y) (A.comparison X)) ⁻¹) (T.idIso _)) then
    (reassociateFour (B.comparison Y ⋆ B.comparison X) (V.comp (S.evaluate X) (S.evaluate Y))
      (V.term (View._⋆_ S (A.comparison Y) (A.comparison X))) (V.term (W.comp (R.evaluate X) (R.evaluate Y)))) ⁻¹ then
    isoComp-cong (T.idIso _)
      ((Operations.vertical-term V kv (View._⋆_ S (A.comparison Y) (A.comparison X))
        (W.comp (R.evaluate X) (R.evaluate Y))) ⁻¹)

-- Structural induction, with no new coherence hypothesis per expression.
-- The inner weakening needs only the minimal core for this theorem.
comparison-composes : {a b : Object} (X : Fun a b)
  → T._=₂_ (C.comparison X) (B.comparison X ∙ V.term (A.comparison X))
comparison-composes (atom f) =
  (isoComp-unitˡ-at _ then OperationCompatibility.identityIso kv (W.map (Interpretation.arrow I f))) ⁻¹
comparison-composes (identity a) = T.idIso _
comparison-composes (composite Y X) = composition-case Y X (comparison-composes Y) (comparison-composes X)
```
