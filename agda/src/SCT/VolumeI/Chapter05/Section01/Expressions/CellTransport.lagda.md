# Transport of second-level operations

The operation comparisons induce third-level identifications for transported cells. These formulas do not assert preservation of the particular proofs used to construct them.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section01.Expressions.TermCalculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations

module SCT.VolumeI.Chapter05.Section01.Expressions.CellTransport {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus.Local T

opaque
  isoInverse-unique : {C D : T.CAT} {f g : T.MAP C D}
    (alpha : T._=₁_ f g) (beta : T._=₁_ g f)
    → T._=₂_ (beta ∙ alpha) (T.idIso f) → T._=₂_ (alpha ⁻¹) beta
  isoInverse-unique alpha beta p = (isoComp-unitˡ-at (alpha ⁻¹)) ⁻¹ then
    isoComp-cong (p ⁻¹) (T.idIso _) then isoComp-assoc-at beta alpha (alpha ⁻¹) then
    isoComp-cong (T.idIso _) (isoComp-inverseʳ-at alpha) then isoComp-unitʳ-at beta

  pre-inverse : {B C D : T.CAT} {f g : T.MAP C D} (alpha : T._=₁_ f g) (r : T.MAP B C)
    → T._=₂_ ((alpha ⁻¹) ▷ r) ((alpha ▷ r) ⁻¹)
  pre-inverse {f = f} alpha r = (isoInverse-unique (alpha ▷ r) ((alpha ⁻¹) ▷ r)
    ((preWhisker-isoComp-at (alpha ⁻¹) alpha r) ⁻¹ then
      (T.preWhisker r ◁ isoComp-inverseˡ-at alpha) then T.preWhisker-idIso f r)) ⁻¹

  post-inverse : {C D E : T.CAT} {f g : T.MAP C D} (u : T.MAP D E) (alpha : T._=₁_ f g)
    → T._=₂_ (u ◁ (alpha ⁻¹)) ((u ◁ alpha) ⁻¹)
  post-inverse {f = f} u alpha = (isoInverse-unique (u ◁ alpha) (u ◁ (alpha ⁻¹))
    ((postWhisker-isoComp-at u (alpha ⁻¹) alpha) ⁻¹ then
      (T.postWhisker u ◁ isoComp-inverseˡ-at alpha) then T.postWhisker-idIso u f)) ⁻¹

  expand : {C D : S.CAT} {f g : S.MAP C D} {alpha beta : S._=₁_ f g}
    (p : S._=₂_ alpha beta)
    → T._=₃_ (cell2 p) ((phi f g ◁ term p) ▷ back)
  expand {f = f} {g} p = T.comp-assoc (term p) (T.postWhisker (phi f g)) (T.preWhisker back)

  vertical : {C D : S.CAT} {f g : S.MAP C D} {alpha beta gamma : S._=₁_ f g}
    (q : S._=₂_ beta gamma) (p : S._=₂_ alpha beta)
    → T._=₃_ (cell2 (S._∙_ q p)) (cell2 q ∙ cell2 p)
  vertical {f = f} {g} q p = expand (S._∙_ q p) then
    (T.preWhisker back ◁ (T.postWhisker (phi f g) ◁ Operations.vertical-term W K q p)) then
    (T.preWhisker back ◁ postWhisker-isoComp-at (phi f g) (term q) (term p)) then
    preWhisker-isoComp-at (phi f g ◁ term q) (phi f g ◁ term p) back then
    isoComp-cong ((expand q) ⁻¹) ((expand p) ⁻¹)

  identity : {C D : S.CAT} {f g : S.MAP C D} (alpha : S._=₁_ f g)
    → T._=₃_ (cell2 (S.idIso alpha)) (T.idIso (term alpha))
  identity {f = f} {g} alpha = expand (S.idIso alpha) then
    (T.preWhisker back ◁ (T.postWhisker (phi f g) ◁ OperationCompatibility.identityIso K alpha)) then
    (T.preWhisker back ◁ T.postWhisker-idIso (phi f g) (map alpha)) then
    T.preWhisker-idIso (phi f g ∘ map alpha) back

  inverse : {C D : S.CAT} {f g : S.MAP C D} {alpha beta : S._=₁_ f g}
    (p : S._=₂_ alpha beta) → T._=₃_ (cell2 (S._⁻¹ p)) ((cell2 p) ⁻¹)
  inverse {f = f} {g} p = expand (S._⁻¹ p) then
    (T.preWhisker back ◁ (T.postWhisker (phi f g) ◁ Calculus.Transport.inverse-term W K p)) then
    (T.preWhisker back ◁ post-inverse (phi f g) (term p)) then
    pre-inverse (phi f g ◁ term p) back then (T.＝-inv ◁ (expand p) ⁻¹)

-- These are actual third-level witnesses derived from operation compatibility.
-- They do not assert preservation of the CHOSEN proofs used to build them.
```
