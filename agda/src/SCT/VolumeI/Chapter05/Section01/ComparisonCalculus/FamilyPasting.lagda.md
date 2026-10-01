# Pasting parameterized comparisons

Vertical pasting and whiskering are carried out for families with arbitrary parameter categories. Their endpoint comparisons are part of each resulting identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.FamilyPasting {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _⁻¹)
open Calculus T
open Operations W using (family; vertical-family; family-const)

opaque
  vertical : {X C D : S.CAT} {f g h : S.MAP C D}
    {f' g' h' : T.MAP (cat C) (cat D)}
    (p : T._=₁_ (map f) f') (q : T._=₁_ (map g) g') (r : T._=₁_ (map h) h')
    (alpha : S.MAP X (S._＝_ f g)) (beta : S.MAP X (S._＝_ g h))
    (alpha' : T.MAP (cat X) (T._＝_ f' g')) (beta' : T.MAP (cat X) (T._＝_ g' h'))
    → T._=₁_ (T.const q ∙ family alpha) (alpha' ∙ T.const p)
    → T._=₁_ (T.const r ∙ family beta) (beta' ∙ T.const q)
    → T._=₁_ (T.const r ∙ family (S._∙_ beta alpha)) ((beta' ∙ alpha') ∙ T.const p)
  vertical p q r alpha beta alpha' beta' first second =
    isoComp-cong (T.idIso _) (vertical-family K beta alpha) then
    (assoc (T.const r) (family beta) (family alpha)) ⁻¹ then
    isoComp-cong second (T.idIso _) then
    assoc beta' (T.const q) (family alpha) then
    isoComp-cong (T.idIso _) first then
    (assoc beta' alpha' (T.const p)) ⁻¹

  constant : {X C D : S.CAT} {f g : S.MAP C D}
    {f' g' : T.MAP (cat C) (cat D)}
    (p : T._=₁_ (map f) f') (q : T._=₁_ (map g) g')
    (alpha : S._=₁_ f g) (beta : T._=₁_ f' g')
    → T._=₂_ (q ∙ term alpha) (beta ∙ p)
    → T._=₁_ (T.const q ∙ family (S.const {P = X} alpha)) (T.const beta ∙ T.const p)
  constant p q alpha beta square =
    isoComp-cong (T.idIso _) (family-const alpha) then
    const-comp q (term alpha) then const-cong square then (const-comp beta p) ⁻¹

-- All inputs and outputs above are functors on the full weakened parameter.
```
