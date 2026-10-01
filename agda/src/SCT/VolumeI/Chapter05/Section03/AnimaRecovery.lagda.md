# Recognizing local animae from their totals

If the total category is an anima, its generic fiber is an anima by
closure under pullbacks. The local recovery equivalence then shows that
the original category is an anima. This direction uses recognition in
the local theory; it does not assert the converse for dependent sums.
Only the local recognition structure and the given recovery data are
needed, rather than the full family of contextual axiom packages.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Generic
import SCT.VolumeI.Chapter05.Section03.GenericFiber as Fiber
import SCT.VolumeI.Chapter05.Section03.Recovery as Recovery
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition

module SCT.VolumeI.Chapter05.Section03.AnimaRecovery
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (PT : Pullbacks.PullbackStructure T)
  (R : Recovery.Recovery W P Q A e (Pullbacks.PullbackStructure.dataPullback PT))
  (MT : Mapping.MappingAnimae T) (FT : Functors.FunctorCategories T MT)
  (I : Walking.WalkingMorphism T) (E : Endpoints.IntervalEndpoints T MT FT PT I)
  (Z : Rezk.RezkAxiom T MT FT PT I E) (AN : Recognition.RecognitionAxiom T MT FT PT I E Z) where

private
  module S = View S
  module T = View T
module Q = Sums.DependentSums Q
module G = Generic W P Q A e using (projection)
module F = Fiber W P Q A e (Pullbacks.PullbackStructure.dataPullback PT) using (local-recovery; fiber-isAn)
module R = Recovery.Recovery R
module Recognize = Recognition.Consequences T MT FT PT I E Z AN using (equivalence-reflects-anima)

total-reflects-anima : (B : T.CAT) → S.isAn (Q.Σ B) → T.isAn B
total-reflects-anima B h = Recognize.equivalence-reflects-anima (F.local-recovery B)
  (R.local-isEquiv B) (F.fiber-isAn (G.projection B) h)
```
