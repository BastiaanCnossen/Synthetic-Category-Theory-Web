# Transport of cones between theories

A cone transports with its specified matching. The comparison with
restriction uses preservation of the associator and of prewhiskering.
These comparisons concern the full cones, not just their projections.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Pasting as Pasting
import SCT.VolumeI.Chapter05.Section01.Expressions.TermCalculus as Terms
import SCT.VolumeI.Chapter01.Section06.Cones as Cones
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ConeTransport
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) where

private
  module S = View S
  module T = View T
module W = Weakening W
module SC = Cones S
module TC = Cones T
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open Pairing T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (cancel-right)

cone : {B C D X : S.CAT} {f : S.MAP B D} {g : S.MAP C D}
  → SC.Cone f g X → TC.Cone (W.map f) (W.map g) (W.cat X)
cone {f = f} {g} s = record
  { left = W.map (SC.Cone.left s) ; right = W.map (SC.Cone.right s)
  ; match = W.comp (SC.Cone.right s) g ∙
      (W.term (SC.Cone.match s) ∙ (W.comp (SC.Cone.left s) f) ⁻¹) }

match-square : {B C D X : S.CAT} {f : S.MAP B D} {g : S.MAP C D}
  (s : SC.Cone f g X)
  → T._=₂_ (W.comp (SC.Cone.right s) g ∙ W.term (SC.Cone.match s))
      (TC.Cone.match (cone s) ∙ W.comp (SC.Cone.left s) f)
match-square {f = f} {g} s =
  (isoComp-assoc-at b (τ ∙ a ⁻¹) a then
    isoComp-cong (T.idIso b) (isoComp-assoc-at τ (a ⁻¹) a then
      isoComp-cong (T.idIso τ) (isoComp-inverseˡ-at a) then isoComp-unitʳ-at τ)) ⁻¹
  where
  a = W.comp (SC.Cone.left s) f
  b = W.comp (SC.Cone.right s) g
  τ = W.term (SC.Cone.match s)

restrict : {B C D X Y : S.CAT} {f : S.MAP B D} {g : S.MAP C D}
  (h : S.MAP X Y) (s : SC.Cone f g Y)
  → TC.ConeIso (cone (SC.conePre h s)) (TC.conePre (W.map h) (cone s))
restrict {Y = Y} {f = f} {g} h s = record
  { leftIso = W.comp h p ; rightIso = W.comp h q
  ; compatible = result }
  where
  p = SC.Cone.left s
  q = SC.Cone.right s
  τ = SC.Cone.match s
  a = (W.map f ◁ W.comp h p) ∙ W.comp (S._∘_ p h) f
  b = (W.map g ◁ W.comp h q) ∙ W.comp (S._∘_ q h) g
  c = (W.comp p f ▷ W.map h) ∙ W.comp h (S._∘_ f p)
  d = (W.comp q g ▷ W.map h) ∙ W.comp h (S._∘_ g q)
  af = S.comp-assoc h p f
  ag = S.comp-assoc h q g
  tf = T.comp-assoc (W.map h) (W.map p) (W.map f)
  tg = T.comp-assoc (W.map h) (W.map q) (W.map g)
  assoc-square : {E F : S.CAT} (u : S.MAP Y E) (v : S.MAP E F)
    → T._=₂_
      (((W.map v ◁ W.comp h u) ∙ W.comp (S._∘_ u h) v) ∙ W.term (S.comp-assoc h u v))
      (T.comp-assoc (W.map h) (W.map u) (W.map v) ∙
        ((W.comp u v ▷ W.map h) ∙ W.comp h (S._∘_ v u)))
  assoc-square u v =
    isoComp-assoc-at (W.map v ◁ W.comp h u) (W.comp (S._∘_ u h) v)
      (W.term (S.comp-assoc h u v)) then OperationCompatibility.associator K h u v
  middle = Pasting.pre W K h (W.comp p f) (W.comp q g) τ
    (TC.Cone.match (cone s)) (match-square s)
  first = Terms.Transport.inverse W K c a af tf (assoc-square p f)
  second = Pasting.vertical W K a c d (S._⁻¹ af) (S._▷_ τ h)
    (tf ⁻¹) (TC.Cone.match (cone s) ▷ W.map h) first middle
  full = Pasting.vertical W K a d b
    (S._∙_ (S._▷_ τ h) (S._⁻¹ af)) ag
    ((TC.Cone.match (cone s) ▷ W.map h) ∙ tf ⁻¹) tg
    second (assoc-square q g)
  result = (cancel-right (W.comp (S._∘_ p h) f)
    (TC.Cone.match (TC.conePre (W.map h) (cone s)) ∙ (W.map f ◁ W.comp h p))) ⁻¹ then
    isoComp-cong
      (isoComp-assoc-at (TC.Cone.match (TC.conePre (W.map h) (cone s)))
        (W.map f ◁ W.comp h p) (W.comp (S._∘_ p h) f) then full ⁻¹)
      (T.idIso _) then
    isoComp-assoc-at b (W.term (SC.Cone.match (SC.conePre h s)))
      ((W.comp (S._∘_ p h) f) ⁻¹) then
    isoComp-assoc-at (W.map g ◁ W.comp h q) (W.comp (S._∘_ q h) g)
      (W.term (SC.Cone.match (SC.conePre h s)) ∙ (W.comp (S._∘_ p h) f) ⁻¹)
```
