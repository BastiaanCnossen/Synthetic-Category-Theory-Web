# Successive weak changes

The transport of a term along two weak changes is compared with transport along their constructed composite. The comparison is a synthetic identification and retains the terminal comparison.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Composition where

open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core

module Two {l : Level} {R S T : Theory l l l}
  (V : Weakening S T) (W : Weakening R S) where
  private
    module R = View R
    module S = View S
    module T = View T
    module V = Weakening V
    module W = Weakening W
    module VW = Weakening (compose V W)
  open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)

  -- Transporting twice agrees with transporting by the constructed composite.
  -- This is a genuine synthetic identification, not host-language equality.
  sequential-term : {C D : R.CAT} {f g : R.MAP C D} (alpha : R._=₁_ f g)
    → T._=₂_ (V.term (W.term alpha)) (VW.term alpha)
  sequential-term {f = f} {g} alpha =
    T.comp-assoc V.back (V.map W.back) ((V.phi (W.map f) (W.map g) ∘ V.map (W.phi f g)) ∘ V.map (W.map alpha)) ∙
    (((T.comp-assoc (V.map (W.map alpha)) (V.map (W.phi f g)) (V.phi (W.map f) (W.map g))) ⁻¹ ▷ V.map W.back) ▷ V.back) ∙
    ((T.comp-assoc (V.map W.back) (V.map (W.phi f g) ∘ V.map (W.map alpha)) (V.phi (W.map f) (W.map g))) ⁻¹ ▷ V.back) ∙
    ((V.phi (W.map f) (W.map g) ◁
       ((V.comp (W.map alpha) (W.phi f g) ▷ V.map W.back) ∙
        V.comp W.back (S._∘_ (W.phi f g) (W.map alpha)))) ▷ V.back)

  -- Underlying inverse functors of transported equivalences agree definitionally.
  -- Their section/retraction witnesses need further compatibility; not asserted.
  inverse-twice : {C D : R.CAT} {f : R.MAP C D} (e : R.IsEquiv f)
    → T._=₁_ (T.IsEquiv.inverse (Results.preservesEquiv V (Results.preservesEquiv W e)))
              (T.IsEquiv.inverse (Results.preservesEquiv (compose V W) e))
  inverse-twice e = T.idIso (V.map (W.map (R.IsEquiv.inverse e)))

module Identity {l : Level} (T : Theory l l l) where
  private
    module T = View T
    module I = Weakening (identity T)
  open T using (_∘_; _∙_; _▷_)

  identity-term : {C D : T.CAT} {f g : T.MAP C D} (alpha : T._=₁_ f g)
    → T._=₂_ (I.term alpha) alpha
  identity-term {f = f} {g} alpha =
    T.comp-unitʳ alpha ∙ (T.comp-unitˡ alpha ▷ T.id T.One)
```
