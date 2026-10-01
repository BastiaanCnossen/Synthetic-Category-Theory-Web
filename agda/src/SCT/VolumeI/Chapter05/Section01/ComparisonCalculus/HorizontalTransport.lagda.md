# Transporting horizontal composites

A horizontal composite is normalized by its precomposition and postcomposition factors. The resulting square retains their endpoint comparisons and the vertical pasting witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.FamilyPasting as Pasting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.HorizontalSquares as SquaresH

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.HorizontalTransport {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _⋆_; _◁_; _⁻¹)
open Calculus T
open Operations W using (family; post-family-square; pre-family-square)

opaque
  unchanged : {X C D : T.CAT} {f g : T.MAP C D} (alpha : T.MAP X (T._＝_ f g))
    → T._=₁_ (T.const (T.idIso g) ∙ alpha) (alpha ∙ T.const (T.idIso f))
  unchanged alpha = unitˡ alpha then (unitʳ alpha) ⁻¹

  raw : {X B C D : S.CAT} {f f' : S.MAP B C} {g g' : S.MAP C D}
    (beta : S.MAP X (S._＝_ g g')) (alpha : S.MAP X (S._＝_ f f'))
    → T._=₁_ (T.const (comp f' g') ∙ family (S._⋆_ beta alpha))
      ((family beta ⋆ family alpha) ∙ T.const (comp f g))
  raw {f = f} {f'} {g} {g'} beta alpha =
    Pasting.vertical W K (comp f g) (comp f' g) (comp f' g')
      (S._◁_ g alpha) (S._▷_ beta f') (map g ◁ family alpha) (T._▷_ (family beta) (map f'))
      (post-family-square K g alpha) (pre-family-square K f' beta)

  horizontal-square : {X B C D : S.CAT} {f f' : S.MAP B C} {g g' : S.MAP C D}
    {F F' : T.MAP (cat B) (cat C)} {G G' : T.MAP (cat C) (cat D)}
    (u : T._=₁_ (map f) F) (v : T._=₁_ (map f') F')
    (p : T._=₁_ (map g) G) (q : T._=₁_ (map g') G')
    (alpha : S.MAP X (S._＝_ f f')) (alpha' : T.MAP (cat X) (T._＝_ F F'))
    (beta : S.MAP X (S._＝_ g g')) (beta' : T.MAP (cat X) (T._＝_ G G'))
    → T._=₁_ (T.const v ∙ family alpha) (alpha' ∙ T.const u)
    → T._=₁_ (T.const q ∙ family beta) (beta' ∙ T.const p)
    → T._=₁_ (T.const ((q ⋆ v) ∙ comp f' g') ∙ family (S._⋆_ beta alpha))
      ((beta' ⋆ alpha') ∙ T.const ((p ⋆ u) ∙ comp f g))
  horizontal-square {f = f} {f'} {g} {g'} u v p q alpha alpha' beta beta' first second =
    Squares.paste T (comp f g) (p ⋆ u) (comp f' g') (q ⋆ v)
      (family (S._⋆_ beta alpha)) (family beta ⋆ family alpha) (beta' ⋆ alpha')
      (raw beta alpha)
      (SquaresH.horizontal-square T u v p q (family alpha) alpha' (family beta) beta' first second)
```
