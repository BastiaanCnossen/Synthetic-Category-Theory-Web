# The normalized identification anima

Endpoint adjustment gives an equivalence on the whole weakened identification anima. The argument does not test only its absolute points.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors
import SCT.VolumeI.Chapter05.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationNormalization as Normalization
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskeringEquivalences

module SCT.VolumeI.Chapter05.Section01.Expressions.IdentificationEquivalence {l : Level} {G : Signature l} {S T : Theory l l l}
  (W : Weakening S T) (I : Interpretation G S) where
private
  module T = View T
  module A = Evaluate I
  module B = Evaluate (image W I)
  module E = Compare W I
  module N = Normalization.One W I
  module W = Weakening W
open T using (_∘_; _∙_; _⁻¹)
open Calculus T
open WhiskeringEquivalences T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv)

opaque
  conjugation : {C D : T.CAT} {f f' g g' : T.MAP C D} (p : T._=₁_ f f') (q : T._=₁_ g g')
    → T.IsEquiv (Coherence.Boundaries.conjugate W p q)
  conjugation p q = T.equiv-transport
    (isoComp-evaluate (T.const q) (T.id _) (rightMultiply (p ⁻¹))
      (const-pre q (rightMultiply (p ⁻¹))) (T.comp-unitˡ (rightMultiply (p ⁻¹))))
    (T.equiv-compose (rightMultiply (p ⁻¹)) (leftMultiply q)
      (rightMultiply-isEquiv (p ⁻¹)) (leftMultiply-isEquiv q))

  action-isEquiv : {a b : Signature.Object G} (X Y : Syntax.Fun G a b)
    → T.IsEquiv (N.action X Y)
  action-isEquiv X Y = T.equiv-compose (W.phi (A.evaluate X) (A.evaluate Y)) (N.adjust X Y)
    (T.Equiv.isEquiv (W.path (A.evaluate X) (A.evaluate Y)))
    (conjugation (E.comparison X) (E.comparison Y))

equivalence : {a b : Signature.Object G} (X Y : Syntax.Fun G a b)
  → T.Equiv (W.cat (View._＝_ S (A.evaluate X) (A.evaluate Y))) (T._＝_ (B.evaluate X) (B.evaluate Y))
equivalence X Y = record { functor = N.action X Y ; isEquiv = action-isEquiv X Y }

-- Endpoint normalization retains an equivalence of the WHOLE internal anima.
-- This does not identify its action on a selected higher witness with an
-- independently chosen target witness, or assert a bijection of external points.
```
