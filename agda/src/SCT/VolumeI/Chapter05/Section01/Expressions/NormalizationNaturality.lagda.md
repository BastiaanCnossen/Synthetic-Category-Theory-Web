# Naturality of endpoint normalization

Endpoint normalization is natural with respect to identifications between input identifications. The comparison is also calculated for successive changes.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Expressions.NormalizationNaturality where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.Expressions.NaturalitySquares as Squares
import SCT.VolumeI.Chapter05.Section01.Expressions.CellTransport as CellTransport
import SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationNormalization as Normalization
import SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationActionComposition as Composition
import SCT.VolumeI.Chapter05.Section01.Expressions.ActionNaturality as Naturality
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WitnessAction as Action

module One {l : Level} {G : Signature l} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) (I : Interpretation G S)
  {a b : Signature.Object G} (X Y : Syntax.Fun G a b) where
  private
    module S = View S
    module T = View T
    module E = Evaluate I
    module W = Weakening W
    module N = Normalization.One W I
  open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
  open Calculus T

  raw : {s t : S._=₁_ (E.evaluate X) (E.evaluate Y)} (p : S._=₂_ s t)
    → T._=₂_ (N.normalize X Y s) (N.normalize X Y t)
  raw p = N.adjust X Y ◁ W.cell2 p

  opaque
    unfolding N.evaluation
    evaluation : {s t : S._=₁_ (E.evaluate X) (E.evaluate Y)} (p : S._=₂_ s t)
      → T._=₃_ (N.evaluation X Y t ∙ Action.Action.congruence W (N.action X Y) p)
        (raw p ∙ N.evaluation X Y s)
    evaluation p = Naturality.One.post W (N.adjust X Y) (W.phi (E.evaluate X) (E.evaluate Y)) p then
      isoComp-cong (T.postWhisker (N.adjust X Y) ◁ (CellTransport.expand W K p) ⁻¹) (T.idIso _)

    vertical : {r s t : S._=₁_ (E.evaluate X) (E.evaluate Y)} (q : S._=₂_ s t) (p : S._=₂_ r s)
      → T._=₃_ (raw (S._∙_ q p)) (raw q ∙ raw p)
    vertical q p = (T.postWhisker (N.adjust X Y) ◁ CellTransport.vertical W K q p) then
      postWhisker-isoComp-at (N.adjust X Y) (W.cell2 q) (W.cell2 p)

    square : {s s' t t' : S._=₁_ (E.evaluate X) (E.evaluate Y)}
      (u : S._=₂_ s s') (v : S._=₂_ t t') (p : S._=₂_ s t) (q : S._=₂_ s' t')
      → S._=₃_ (S._∙_ v p) (S._∙_ q u)
      → T._=₃_ (raw v ∙ raw p) (raw q ∙ raw u)
    square u v p q witness = (vertical v p) ⁻¹ then
      (T.postWhisker (N.adjust X Y) ◁ W.cell3 witness) then vertical q u

module Two {l : Level} {G : Signature l} {R S T : Theory l l l}
  (V : Weakening S T) (W : Weakening R S) (kv : OperationCompatibility V)
  (kw : OperationCompatibility W) (kc : OperationCompatibility (compose V W))
  (I : Interpretation G R) {a b : Signature.Object G} (X Y : Syntax.Fun G a b) where
  private
    module R = View R
    module T = View T
    module E = Evaluate I
    module V = Weakening V
    module VW = Weakening (compose V W)
    module NW = Normalization.One W I
    module NV = Normalization.One V (image W I)
    module NC = Normalization.One (compose V W) I
    module RW = One W kw I X Y
    module RV = One V kv (image W I) X Y
    module RC = One (compose V W) kc I X Y
    module AC = Composition V W kv I using (point-composes; action-composes)
  open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
  open Calculus T

  module At {s t : R._=₁_ (E.evaluate X) (E.evaluate Y)} (p : R._=₂_ s t) where
    private
      wa = NW.action X Y
      va = NV.action X Y
      ca = NC.action X Y
      joined = va ∘ V.map wa
      d = AC.action-composes X Y
      p0 = RC.raw p
      p1 = Action.Action.congruence (compose V W) ca p
      p2 = Action.Action.congruence (compose V W) joined p
      p3 = Action.Action.congruence V va (Action.Action.congruence W wa p)
      p4 = Action.Action.congruence V va (RW.raw p)
      p5 = RV.raw (RW.raw p)
      s1 = λ z → (NC.evaluation X Y z) ⁻¹
      s2 = λ z → (d ▷ VW.map z) ▷ VW.back
      s3 = λ z → (Action.Two.sequential V W wa va z) ⁻¹
      s4 = λ z → Action.Action.congruence V va (NW.evaluation X Y z)
      s5 = λ z → NV.evaluation X Y (NW.normalize X Y z)

    opaque
      unfolding AC.point-composes
      point-composes : T._=₃_ (AC.point-composes X Y t ∙ RC.raw p)
        (RV.raw (RW.raw p) ∙ AC.point-composes X Y s)
      point-composes = Squares.paste T (s1 s) ((s5 s ∙ (s4 s ∙ s3 s)) ∙ s2 s)
        (s1 t) ((s5 t ∙ (s4 t ∙ s3 t)) ∙ s2 t) p0 p1 p5
        (Squares.inverse-boundary T _ _ _ _ (RC.evaluation p))
        (Squares.paste T (s2 s) (s5 s ∙ (s4 s ∙ s3 s)) (s2 t) (s5 t ∙ (s4 t ∙ s3 t)) p1 p2 p5
          (Naturality.One.comparison (compose V W) d p)
          (Squares.paste T (s4 s ∙ s3 s) (s5 s) (s4 t ∙ s3 t) (s5 t) p2 p4 p5
            (Squares.paste T (s3 s) (s4 s) (s3 t) (s4 t) p2 p3 p4
              (Squares.inverse-boundary T _ _ _ _ (Naturality.Two.sequential V W kv wa va p))
              (Naturality.One.square V kv va _ _ _ _ (RW.evaluation p)))
            (RV.evaluation (RW.raw p))))

  point-composes : {s t : R._=₁_ (E.evaluate X) (E.evaluate Y)} (p : R._=₂_ s t)
    → T._=₃_ (AC.point-composes X Y t ∙ RC.raw p)
      (RV.raw (RW.raw p) ∙ AC.point-composes X Y s)
  point-composes p = At.point-composes p
```
