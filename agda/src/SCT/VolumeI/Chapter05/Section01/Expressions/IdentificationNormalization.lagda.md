# Normalizing identifications

Functor-expression comparisons adjust the two endpoints of an arbitrary identification. This first-level normalization composes, with explicit comparison identifications; normalization of a witness between chosen identification expressions is a further level.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationNormalization where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors
import SCT.VolumeI.Chapter05.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares
import SCT.VolumeI.Chapter05.Section01.Expressions.TermCalculus as Calculus
import SCT.VolumeI.Chapter05.Section01.Expressions.FunctorComposition as FunctorComposition
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Composition as Composition
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WitnessAction as Action

module One {l : Level} {G : Signature l} {S T : Theory l l l}
  (W : Weakening S T) (I : Interpretation G S) where
  private
    module S = View S
    module T = View T
    module A = Evaluate I
    module B = Evaluate (image W I)
  open Signature G
  open Syntax G
  open Compare W I using (comparison)
  open Weakening W
  open Calculus.Local T
  open T using (_⁻¹)

  adjust : {a b : Object} (X Y : Fun a b)
    → T.MAP (T._＝_ (map (A.evaluate X)) (map (A.evaluate Y))) (T._＝_ (B.evaluate X) (B.evaluate Y))
  adjust X Y = Coherence.Boundaries.conjugate W (comparison X) (comparison Y)

  normalize : {a b : Object} (X Y : Fun a b)
    → S._=₁_ (A.evaluate X) (A.evaluate Y) → T._=₁_ (B.evaluate X) (B.evaluate Y)
  normalize X Y alpha = T._∘_ (adjust X Y) (term alpha)

  action : {a b : Object} (X Y : Fun a b)
    → T.MAP (cat (S._＝_ (A.evaluate X) (A.evaluate Y))) (T._＝_ (B.evaluate X) (B.evaluate Y))
  action X Y = T._∘_ (adjust X Y) (phi (A.evaluate X) (A.evaluate Y))

  opaque
    evaluation : {a b : Object} (X Y : Fun a b) (alpha : S._=₁_ (A.evaluate X) (A.evaluate Y))
      → T._=₂_ (Action.Action.act W (action X Y) alpha) (normalize X Y alpha)
    evaluation X Y alpha = Action.Action.post W (adjust X Y) (phi (A.evaluate X) (A.evaluate Y)) alpha

    family-square : {a b : Object} (X Y : Fun a b)
      → T._=₁_ (T._∙_ (T.const (comparison Y)) (phi (A.evaluate X) (A.evaluate Y)))
        (T._∙_ (action X Y) (T.const (comparison X)))
    family-square X Y = Squares.unsolve T (comparison X) (comparison Y)
      (phi (A.evaluate X) (A.evaluate Y)) (action X Y) (T.idIso _)

  opaque
    square : {a b : Object} (X Y : Fun a b) (alpha : S._=₁_ (A.evaluate X) (A.evaluate Y))
      → T._=₂_ (T._∙_ (comparison Y) (term alpha)) (T._∙_ (normalize X Y alpha) (comparison X))
    square X Y alpha = isoComp-cong ((const-One (comparison Y)) ⁻¹) (T.idIso _) then
      Squares.unsolve T (comparison X) (comparison Y) (term alpha) (normalize X Y alpha) (T.idIso _) then
      isoComp-cong (T.idIso _) (const-One (comparison X))

module Two {l : Level} {G : Signature l} {R S T : Theory l l l}
  (V : Weakening S T) (W : Weakening R S) (kv : OperationCompatibility V) (I : Interpretation G R) where
  private
    module R = View R
    module T = View T
    module E = Evaluate I
    module A = Compare W I
    module B = Compare V (image W I)
    module C = Compare (compose V W) I
    module NW = One W I
    module NV = One V (image W I)
    module NC = One (compose V W) I
    module V = Weakening V
    module W = Weakening W
    module VW = Weakening (compose V W)
    module FC = FunctorComposition V W kv I using (comparison-composes)
  open Signature G
  open Syntax G renaming (compose to composite)
  open T using (_∙_; _⁻¹)
  open Calculus.Local T

  opaque
    successive-square : {a b : Object} (X Y : Fun a b)
      (alpha : R._=₁_ (E.evaluate X) (E.evaluate Y))
      → T._=₂_ (C.comparison Y ∙ VW.term alpha)
        (NV.normalize X Y (NW.normalize X Y alpha) ∙ C.comparison X)
    successive-square X Y alpha =
      isoComp-cong (FC.comparison-composes Y) ((Composition.Two.sequential-term V W alpha) ⁻¹) then
      isoComp-assoc-at (B.comparison Y) (V.term (A.comparison Y)) (V.term (W.term alpha)) then
      isoComp-cong (T.idIso _)
        ((Operations.vertical-term V kv (A.comparison Y) (W.term alpha)) ⁻¹ then
          V.cell2 (NW.square X Y alpha) then
          Operations.vertical-term V kv (NW.normalize X Y alpha) (A.comparison X)) then
      (isoComp-assoc-at (B.comparison Y) (V.term (NW.normalize X Y alpha)) (V.term (A.comparison X))) ⁻¹ then
      isoComp-cong (NV.square X Y (NW.normalize X Y alpha)) (T.idIso _) then
      isoComp-assoc-at (NV.normalize X Y (NW.normalize X Y alpha)) (B.comparison X) (V.term (A.comparison X)) then
      isoComp-cong (T.idIso _) ((FC.comparison-composes X) ⁻¹)

    normalization-composes : {a b : Object} (X Y : Fun a b)
      (alpha : R._=₁_ (E.evaluate X) (E.evaluate Y))
      → T._=₂_ (NC.normalize X Y alpha) (NV.normalize X Y (NW.normalize X Y alpha))
    normalization-composes X Y alpha = Squares.term-solve T (C.comparison X) (C.comparison Y)
      (VW.term alpha) (NV.normalize X Y (NW.normalize X Y alpha)) (successive-square X Y alpha)

-- This theorem is for ANY identification alpha, with arbitrary functor
-- expression endpoints. It is one dimension below normalization of a
-- pentagonator between two chosen identification EXPRESSIONS.
```
