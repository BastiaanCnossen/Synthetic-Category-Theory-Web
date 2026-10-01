# The generic fiber of an absolute pullback

Weakening takes the chosen absolute pullback cone to a local pullback
cone. Pasting with the generic point identifies the generic fiber of
its first projection with the pullback over the represented point.
The pasting theorem retains the matching of the transported cone.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.PullbackPreservation as Preservation
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.Pasting.UniversalNestedPullbacks as Nested

module SCT.VolumeI.Chapter05.Section04.SubstitutionCalculus.PullbackFibers
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (PS : Pullbacks.PullbackStructure S) (PT : Pullbacks.PullbackStructure T)
  (PW : Preservation.PreservesPullbacks W (Pullbacks.PullbackStructure.dataPullback PS)
    (Pullbacks.PullbackStructure.dataPullback PT))
  {A B X : View.CAT S} (g : View.MAP S B A) (p : View.MAP S X A)
  (b : View.MAP T (View.One T) (Weakening.cat W B)) where

private
  module S = View S
  module T = View T
module W = Weakening W
module PS = Pullbacks.PullbackStructure PS
module PT = Pullbacks.PullbackStructure PT
module Transport = Preservation W PS.dataPullback PT.dataPullback
module N = Nested.Nested T PT b (W.map g) (W.map p)
  (Transport.cone (PS.pullbackCone g p))
  (Transport.PreservesPullbacks.comparison-isEquiv PW g p)
  using (flatten; flatten-isEquiv; β)

comparison : T.MAP (PT.Pullback b (W.map (PS.pullback₁ {f = g} {p})))
  (PT.Pullback (T._∘_ (W.map g) b) (W.map p))
comparison = N.flatten

opaque
  comparison-isEquiv : T.IsEquiv comparison
  comparison-isEquiv = N.flatten-isEquiv

inclusion : T._=₁_ (T._∘_ PT.pullback₂ comparison)
  (T._∘_ (W.map (PS.pullback₂ {f = g} {p})) PT.pullback₂)
inclusion = N.β
```
