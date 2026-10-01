# Naturality of witness action

Action on a witness respects identifications in its source anima. The successive-action comparison is natural in that witness, with the terminal comparison retained.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Expressions.ActionNaturality where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.Expressions.NaturalitySquares as Squares
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WitnessAction as Action
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Composition as Composition

module One {l : Level} {S T : Theory l l l} (W : Weakening S T) where
  private
    module S = View S
    module T = View T
  open Weakening W
  open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
  open Calculus T

  opaque
    vertical : (K : OperationCompatibility W) {X : S.CAT} {Y : T.CAT}
      (a : T.MAP (cat X) Y) {x y z : S.Obj-abs X}
      (q : S._=₁_ y z) (p : S._=₁_ x y)
      → T._=₂_ (Action.Action.congruence W a (S._∙_ q p))
        (Action.Action.congruence W a q ∙ Action.Action.congruence W a p)
    vertical K a q p =
      (T.preWhisker back ◁ (T.postWhisker a ◁ Operations.vertical-term W K q p)) then
      (T.preWhisker back ◁ postWhisker-isoComp-at a (term q) (term p)) then
      preWhisker-isoComp-at (a ◁ term q) (a ◁ term p) back

    square : (K : OperationCompatibility W) {X : S.CAT} {Y : T.CAT}
      (a : T.MAP (cat X) Y) {x x' y y' : S.Obj-abs X}
      (u : S._=₁_ x x') (v : S._=₁_ y y') (p : S._=₁_ x y) (q : S._=₁_ x' y')
      → S._=₂_ (S._∙_ v p) (S._∙_ q u)
      → T._=₂_ (Action.Action.congruence W a v ∙ Action.Action.congruence W a p)
        (Action.Action.congruence W a q ∙ Action.Action.congruence W a u)
    square K a u v p q witness = (vertical K a v p) ⁻¹ then
      (T.preWhisker back ◁ (T.postWhisker a ◁ cell2 witness)) then vertical K a q u

    post : {X : S.CAT} {Y Z : T.CAT}
      (b : T.MAP Y Z) (a : T.MAP (cat X) Y)
      {x y : S.Obj-abs X} (p : S._=₁_ x y)
      → T._=₂_ (Action.Action.post W b a y ∙ Action.Action.congruence W (b ∘ a) p)
        ((b ◁ Action.Action.congruence W a p) ∙ Action.Action.post W b a x)
    post b a {x} {y} p = Squares.paste T
      (T.comp-assoc (map x) a b ▷ back) (T.comp-assoc back (a ∘ map x) b)
      (T.comp-assoc (map y) a b ▷ back) (T.comp-assoc back (a ∘ map y) b)
      (((b ∘ a) ◁ term p) ▷ back) ((b ◁ (a ◁ term p)) ▷ back)
      (b ◁ ((a ◁ term p) ▷ back))
      (Squares.pre T (T.comp-assoc (map x) a b) (T.comp-assoc (map y) a b)
        ((b ∘ a) ◁ term p) (b ◁ (a ◁ term p)) (postWhisker-comp-at (term p) a b) back)
      (whisker-mixed-at (a ◁ term p) back b)

    comparison : {X : S.CAT} {Y : T.CAT}
      {a b : T.MAP (cat X) Y} (d : T._=₁_ a b)
      {x y : S.Obj-abs X} (p : S._=₁_ x y)
      → T._=₂_ (((d ▷ map y) ▷ back) ∙ Action.Action.congruence W a p)
        (Action.Action.congruence W b p ∙ ((d ▷ map x) ▷ back))
    comparison d {x} {y} p = Squares.pre T (d ▷ map x) (d ▷ map y)
      (_ ◁ term p) (_ ◁ term p) (interchange-at d (term p)) back

module Two {l : Level} {R S T : Theory l l l}
  (V : Weakening S T) (W : Weakening R S) (K : OperationCompatibility V) where
  private
    module R = View R
    module S = View S
    module T = View T
    module V = Weakening V
    module W = Weakening W
    module VW = Weakening (compose V W)
  open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
  open Calculus T

  module At {X : R.CAT} {Y : S.CAT} {Z : T.CAT}
    (a : S.MAP (W.cat X) Y) (b : T.MAP (V.cat Y) Z)
    {x y : R.Obj-abs X} (p : R._=₁_ x y) where
    private
      wx = W.map x
      wy = W.map y
      wp = W.term p
      vb = V.back
      wb = V.map W.back
      va = V.map a
      q = V.term wp
      c = b ∘ va
      p0 = Action.Action.congruence V b (Action.Action.congruence W a p)
      p1 = (b ◁ (V.term (S._◁_ a wp) ▷ wb)) ▷ vb
      p2 = (b ◁ ((va ◁ q) ▷ wb)) ▷ vb
      p3 = ((b ◁ (va ◁ q)) ▷ wb) ▷ vb
      p4 = ((c ◁ q) ▷ wb) ▷ vb
      p5 = (c ◁ q) ▷ (wb ∘ vb)
      s1 = λ (z : R.Obj-abs X) → (b ◁ V.comp W.back (S._∘_ a (W.map z))) ▷ vb
      s2 = λ (z : R.Obj-abs X) → (b ◁ (V.comp (W.map z) a ▷ wb)) ▷ vb
      s3 = λ (z : R.Obj-abs X) → (T.comp-assoc wb (va ∘ V.map (W.map z)) b) ⁻¹ ▷ vb
      s4 = λ (z : R.Obj-abs X) → ((T.comp-assoc (V.map (W.map z)) va b) ⁻¹ ▷ wb) ▷ vb
      s5 = λ (z : R.Obj-abs X) → T.comp-assoc vb wb (c ∘ V.map (W.map z))

    opaque
      step1 : T._=₂_ (s1 y ∙ p0) (p1 ∙ s1 x)
      step1 = Squares.pre T _ _ _ _
        (Squares.post T _ _ _ _ (Operations.pre-term-square V K W.back (S._◁_ a wp)) b) vb

      step2 : T._=₂_ (s2 y ∙ p1) (p2 ∙ s2 x)
      step2 = Squares.pre T _ _ _ _
        (Squares.post T _ _ _ _
          (Squares.pre T _ _ _ _ (Operations.post-term-square V K a wp) wb) b) vb

      step3 : T._=₂_ (s3 y ∙ p2) (p3 ∙ s3 x)
      step3 = Squares.pre T _ _ _ _
        (Squares.inverse-boundary T _ _ _ _ (whisker-mixed-at (va ◁ q) wb b)) vb

      step4 : T._=₂_ (s4 y ∙ p3) (p4 ∙ s4 x)
      step4 = Squares.pre T _ _ _ _
        (Squares.pre T _ _ _ _
          (Squares.inverse-boundary T _ _ _ _ (postWhisker-comp-at q va b)) wb) vb

      step5 : T._=₂_ (s5 y ∙ p4) (p5 ∙ s5 x)
      step5 = preWhisker-comp-at (c ◁ q) wb vb

      sequential : T._=₂_
        (Action.Two.sequential V W a b y ∙ p0)
        (Action.Action.congruence (compose V W) (b ∘ V.map a) p ∙ Action.Two.sequential V W a b x)
      sequential =
        Squares.paste T _ _ _ _ p0 p4 p5
          (Squares.paste T _ _ _ _ p0 p3 p4
            (Squares.paste T _ _ _ _ p0 p2 p3
              (Squares.paste T _ _ _ _ p0 p1 p2 step1 step2) step3) step4) step5 then
        isoComp-cong
          (T.preWhisker (wb ∘ vb) ◁ (T.postWhisker c ◁ Composition.Two.sequential-term V W p))
          (T.idIso _)

  sequential : {X : R.CAT} {Y : S.CAT} {Z : T.CAT}
    (a : S.MAP (W.cat X) Y) (b : T.MAP (V.cat Y) Z)
    {x y : R.Obj-abs X} (p : R._=₁_ x y)
    → T._=₂_
      (Action.Two.sequential V W a b y ∙ Action.Action.congruence V b (Action.Action.congruence W a p))
      (Action.Action.congruence (compose V W) (b ∘ V.map a) p ∙ Action.Two.sequential V W a b x)
  sequential a b p = At.sequential a b p
```
