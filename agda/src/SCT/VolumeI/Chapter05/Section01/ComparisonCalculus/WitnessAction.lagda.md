# Action on selected witnesses

A witness is a term in its identification anima. Its image therefore uses both the comparison of that anima and the terminal comparison. Congruence and successive action are proved for this construction.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WitnessAction where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module Action {l : Level} {S T : Theory l l l} (W : Weakening S T) where
  private
    module S = View S
    module T = View T
  open Weakening W
  open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
  open Calculus T using (_then_)

  act : {X : S.CAT} {Y : T.CAT} → T.MAP (cat X) Y → S.Obj-abs X → T.Obj-abs Y
  act a x = (a ∘ map x) ∘ back

  congruence : {X : S.CAT} {Y : T.CAT} (a : T.MAP (cat X) Y)
    {x y : S.Obj-abs X} → S._=₁_ x y → T._=₁_ (act a x) (act a y)
  congruence a p = (a ◁ term p) ▷ back

  post : {X : S.CAT} {Y Z : T.CAT} (b : T.MAP Y Z) (a : T.MAP (cat X) Y)
    (x : S.Obj-abs X) → T._=₁_ (act (b ∘ a) x) (b ∘ act a x)
  post b a x = (T.comp-assoc (map x) a b ▷ back) then
    T.comp-assoc back (a ∘ map x) b

module Two {l : Level} {R S T : Theory l l l} (V : Weakening S T) (W : Weakening R S) where
  private
    module R = View R
    module S = View S
    module T = View T
    module V = Weakening V
    module W = Weakening W
    module VW = Weakening (compose V W)
  open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
  open Calculus T using (_then_)

  sequential : {X : R.CAT} {Y : S.CAT} {Z : T.CAT}
    (a : S.MAP (W.cat X) Y) (b : T.MAP (V.cat Y) Z) (x : R.Obj-abs X)
    → T._=₁_ (Action.act V b (Action.act W a x))
      (Action.act (compose V W) (b ∘ V.map a) x)
  sequential a b x =
    ((b ◁ V.comp W.back (S._∘_ a (W.map x))) ▷ V.back) then
    ((b ◁ (V.comp (W.map x) a ▷ V.map W.back)) ▷ V.back) then
    ((T.comp-assoc (V.map W.back) (V.map a ∘ V.map (W.map x)) b) ⁻¹ ▷ V.back) then
    (((T.comp-assoc (V.map (W.map x)) (V.map a) b) ⁻¹ ▷ V.map W.back) ▷ V.back) then
    T.comp-assoc V.back (V.map W.back) ((b ∘ V.map a) ∘ V.map (W.map x))

  preserves : {X : R.CAT} {Y : S.CAT} {Z : T.CAT}
    (a : S.MAP (W.cat X) Y) (b : T.MAP (V.cat Y) Z)
    (x : R.Obj-abs X) (y : S.Obj-abs Y) (z : T.Obj-abs Z)
    → S._=₁_ (Action.act W a x) y → T._=₁_ (Action.act V b y) z
    → T._=₁_ (Action.act (compose V W) (b ∘ V.map a) x) z
  preserves a b x y z first second = (sequential a b x) ⁻¹ then
    Action.congruence V b first then second

  -- A comparison with another, independently selected action must be supplied
  -- or proved. This lemma does not construct that comparison.
  compare-action : {X : R.CAT} {Y : S.CAT} {Z : T.CAT}
    (a : S.MAP (W.cat X) Y) (b : T.MAP (V.cat Y) Z)
    (c : T.MAP (VW.cat X) Z) (x : R.Obj-abs X) (z : T.Obj-abs Z)
    → T._=₁_ c (b ∘ V.map a)
    → T._=₁_ (Action.act (compose V W) (b ∘ V.map a) x) z
    → T._=₁_ (Action.act (compose V W) c x) z
  compare-action a b c x z comparison preservation =
    ((comparison ▷ VW.map x) ▷ VW.back) then preservation
```
