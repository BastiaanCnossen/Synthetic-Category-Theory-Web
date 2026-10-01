# Recovery in the terminal anima context

The pair functor is an equivalence when the base anima is terminal.
The proof passes through generic-fiber recovery and the pullback of an
equivalence. It does not identify the two theories definitionally.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point
import SCT.VolumeI.Chapter05.Section03.GenericFiber as Fiber
import SCT.VolumeI.Chapter05.Section03.Recovery as Recovery
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences as PullbackEquiv
import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry as Symmetry

module SCT.VolumeI.Chapter05.Section03.TerminalContext
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.One S))
  (PB : Pullbacks.PullbackStructure T)
  (R : Recovery.Recovery W P Q (record { category = View.One S ; witness = View.one-isAn S })
    e (Pullbacks.PullbackStructure.dataPullback PB)) where

private
  module S = View S
  module T = View T
  A : S.AN
  A = record { category = S.One ; witness = S.one-isAn }
module W = Weakening W
module Q = Sums.DependentSums Q
module G = Point W P Q A e using (generic; projection)
module F = Fiber W P Q A e (Pullbacks.PullbackStructure.dataPullback PB)
  using (Fiber; local-recovery; local-recovery-β; fiber-inclusion)
module R = Recovery.Recovery R
open Pullbacks.PullbackStructure PB
open T using (_∘_; _∙_; _⁻¹)
open PullbackEquiv T PB using (pullback-equivalence)
open Symmetry T PB using (pullback-equivalenceʳ)

generic-isEquiv : T.IsEquiv G.generic
generic-isEquiv = T.equiv-cancel-left G.generic (T.Equiv.functor W.terminal)
  (T.Equiv.isEquiv W.terminal)
  (T.equiv-transport (T.terminal-iso (T.id T.One) _) (T.id-isEquiv T.One))

fiber-inclusion-isEquiv : {X : S.CAT} (p : S.MAP X S.One)
  → T.IsEquiv (F.fiber-inclusion p)
fiber-inclusion-isEquiv p = pullback-equivalenceʳ G.generic (W.map p) generic-isEquiv

pair-isEquiv : (B : T.CAT) → T.IsEquiv (Q.pair B)
pair-isEquiv B = T.equiv-transport (F.local-recovery-β B)
  (T.equiv-compose (F.local-recovery B) (F.fiber-inclusion (G.projection B))
    (R.local-isEquiv B) (fiber-inclusion-isEquiv (G.projection B)))

local-equivalence : (B : T.CAT) → T.Equiv B (W.cat (Q.Σ B))
local-equivalence B = record { functor = Q.pair B ; isEquiv = pair-isEquiv B }
```
