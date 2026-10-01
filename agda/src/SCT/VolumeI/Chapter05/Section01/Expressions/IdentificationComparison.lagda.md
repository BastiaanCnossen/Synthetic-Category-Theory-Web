# Comparing identification expressions

Recursion on an identification expression constructs its comparison from the primitive operation comparisons. Every constructor has a fixed proof clause, so the selected comparison is retained for later coherence questions.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors
open import SCT.VolumeI.Chapter05.Section01.Expressions.Identifications
import SCT.VolumeI.Chapter05.Section01.Expressions.TermCalculus as Calculus
import SCT.VolumeI.Chapter05.Section01.Expressions.StructuralSquares as Structural
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Pasting as Pasting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares
import SCT.VolumeI.Chapter05.Section01.Coherence as Coherence

module SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationComparison {l : Level} {G : Signature l} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) (I : Interpretation G S) where
private
  module S = View S
  module T = View T
  module A = Evaluate I
  module B = Evaluate (image W I)
  module AS = Interpret I
  module BT = Interpret (image W I)
  module SC = Calculus.Local S
open Weakening W
open Signature G
open Syntax G
open Cells G
open Compare W I using (comparison)
open T using (_∙_; _⁻¹)
open Calculus.Local T

-- Every constructor has a fixed proof clause. This is not a lookup table of
-- normalization assumptions for complete expressions.
square : {a b : Object} {X Y : Fun a b} (s : Iso X Y)
  → T._=₂_ (comparison Y ∙ term (AS.evaluate-cell s)) (BT.evaluate-cell s ∙ comparison X)
square (identity-cell X) = Calculus.Transport.identity-square W K (A.evaluate X) (comparison X)
square (vertical {X = X} {Y} {Z} q p) = Pasting.vertical W K (comparison X) (comparison Y) (comparison Z)
  (AS.evaluate-cell p) (AS.evaluate-cell q) (BT.evaluate-cell p) (BT.evaluate-cell q) (square p) (square q)
square (inverse {X = X} {Y} p) = Calculus.Transport.inverse W K (comparison X) (comparison Y)
  (AS.evaluate-cell p) (BT.evaluate-cell p) (square p)
square (horizontal {X = X} {X'} {Y} {Y'} q p) = Calculus.Transport.horizontal W K
  (comparison X) (comparison X') (comparison Y) (comparison Y')
  (AS.evaluate-cell p) (BT.evaluate-cell p) (AS.evaluate-cell q) (BT.evaluate-cell q) (square p) (square q)
square (post {X = X} {X'} Y p) =
  isoComp-cong (T.idIso _) (cell2 ((SC.hcomp-idOuter (A.evaluate Y) (AS.evaluate-cell p)) S.⁻¹)) then
  Calculus.Transport.horizontal W K (comparison X) (comparison X') (comparison Y) (comparison Y)
    (AS.evaluate-cell p) (BT.evaluate-cell p) (S.idIso (A.evaluate Y)) (T.idIso (B.evaluate Y))
    (square p) (Calculus.Transport.identity-square W K (A.evaluate Y) (comparison Y)) then
  isoComp-cong (hcomp-idOuter (B.evaluate Y) (BT.evaluate-cell p)) (T.idIso _)
square (pre {Y = Y} {Y'} p X) =
  isoComp-cong (T.idIso _) (cell2 ((SC.hcomp-idInner (AS.evaluate-cell p) (A.evaluate X)) S.⁻¹)) then
  Calculus.Transport.horizontal W K (comparison X) (comparison X) (comparison Y) (comparison Y')
    (S.idIso (A.evaluate X)) (T.idIso (B.evaluate X)) (AS.evaluate-cell p) (BT.evaluate-cell p)
    (Calculus.Transport.identity-square W K (A.evaluate X) (comparison X)) (square p) then
  isoComp-cong (hcomp-idInner (BT.evaluate-cell p) (B.evaluate X)) (T.idIso _)
square (associator X Y Z) = Structural.Associator.square W K (A.evaluate X) (A.evaluate Y) (A.evaluate Z)
  (comparison X) (comparison Y) (comparison Z)
square (left-unit X) = Structural.left-unit W K (A.evaluate X) (comparison X)
square (right-unit X) = Structural.right-unit W K (A.evaluate X) (comparison X)

adjust : {a b : Object} (X Y : Fun a b)
  → T.MAP (T._＝_ (map (A.evaluate X)) (map (A.evaluate Y))) (T._＝_ (B.evaluate X) (B.evaluate Y))
adjust X Y = Coherence.Boundaries.conjugate W (comparison X) (comparison Y)

opaque
  normalized : {a b : Object} {X Y : Fun a b} (s : Iso X Y)
    → T._=₂_ (T._∘_ (adjust X Y) (term (AS.evaluate-cell s))) (BT.evaluate-cell s)
  normalized {X = X} {Y} s = Squares.term-solve T (comparison X) (comparison Y)
    (term (AS.evaluate-cell s)) (BT.evaluate-cell s) (square s)
```
