# The pair squares are pullbacks

Paste the pair square of a local functor with the recovery square of its
target. The sum universal property supplies an auxiliary identification
between the two total projections whose restriction compares the outer
rectangle with the source recovery square. Its computation is retained
at the level of identifications between identifications. Pullback
cancellation then applies to the original pair square.

The auxiliary identification is used only in this argument. The square
proved cartesian has the specified `Σ-map-β` matching; no comparison with
the separately chosen projection-naturality identification is needed here.
Consequently, if the dependent sum of a local functor is an equivalence,
the original local functor is an equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.Core as Core
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.Expressions.EndpointTransport as Endpoints
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumIdentifications as Identifications
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point
import SCT.VolumeI.Chapter05.Section03.GenericFiber as Fiber
import SCT.VolumeI.Chapter05.Section03.Recovery as Recovery
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackSquares as Squares
import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry as Symmetry
import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences as PullbackEquivalences
import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange as ArrowChange
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange as ConeChange
import SCT.VolumeI.Chapter01.Section06.PastingLemma as Pasting
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing

module SCT.VolumeI.Chapter05.Section03.PairPullbacks
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W)
  (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (PT : Pullbacks.PullbackStructure T)
  (R : Recovery.Recovery W P Q A e (Pullbacks.PullbackStructure.dataPullback PT)) where

private
  module S = View S
  module T = View T
module W = Weakening W
module Q = Sums.DependentSums Q
module QA = Action W P Q using (Σ-map; Σ-map-β; reflect)
module SI = Identifications W K P Q using (action; reflect-β)
module G = Point W P Q A e using (projection; generic)
module F = Fiber W P Q A e (Pullbacks.PullbackStructure.dataPullback PT) using (recovery-cone)
module R = Recovery.Recovery R
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_; isoComp-cong; isoComp-assoc-at;
  isoComp-inverseʳ-at; isoComp-unitˡ-at; isoComp-unitʳ-at; preWhisker-isoComp-at)
open Squares T PT using (Cone; ConeIso; IsPullback; pullback-cone-invariant; coneIso-inverse)
open ConeChange T using (coneSwap; coneSwap-swap; changeLeft)
open Symmetry T PT using (pullback-swap)
open Pairing T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (cancel-right)

module Naturality {B C : T.CAT} (f : T.MAP B C) where

  square : Cone (Q.pair C) (W.map (QA.Σ-map f)) B
  square = record { left = f ; right = Q.pair B ; match = QA.Σ-map-β f }

  private
    target-recovery = coneSwap (F.recovery-cone C)
    source-recovery = coneSwap (F.recovery-cone B)

  module Paste = Pasting.Pasting T PT (W.map (QA.Σ-map f))
    (W.map (G.projection C)) G.generic target-recovery
    (pullback-swap (F.recovery-cone C) (R.local-isEquiv C))
    using (module Paste; cancel-isPullback)

  private
    outer = Paste.Paste.flatten (coneSwap square)
    M = Cone.match outer
    b = Cone.match source-recovery
    ε = T.terminal-iso (T.terminate C ∘ f) (T.terminate B)
    n = (G.generic ◁ ε) ∙ M
    a₀ = (W.comp (QA.Σ-map f) (G.projection C)) ⁻¹
    a = a₀ ▷ Q.pair B
    α = Endpoints.changeEndpoints T a (b ⁻¹) n

  auxiliary-triangle : S._=₁_ (S._∘_ (G.projection C) (QA.Σ-map f)) (G.projection B)
  auxiliary-triangle = QA.reflect α

  private
    δ = W.term auxiliary-triangle ∙ a₀
    d = δ ▷ Q.pair B

    restriction-square : T._=₂_ ((b ⁻¹) ∙ n) (SI.action auxiliary-triangle ∙ a)
    restriction-square = Endpoints.changeEndpoints-to-square T a (b ⁻¹) n
      (SI.action auxiliary-triangle) ((SI.reflect-β α) ⁻¹)

    matching-computation : T._=₂_ (b ∙ d) n
    matching-computation = isoComp-cong (T.idIso b)
      (preWhisker-isoComp-at (W.term auxiliary-triangle) a₀ (Q.pair B) then
        restriction-square ⁻¹) then
      (isoComp-assoc-at b (b ⁻¹) n) ⁻¹ then
      isoComp-cong (isoComp-inverseʳ-at b) (T.idIso n) then isoComp-unitˡ-at n

    recovery-comparison : ConeIso (changeLeft δ outer) source-recovery
    recovery-comparison = record
      { leftIso = T.idIso (Q.pair B) ; rightIso = ε
      ; compatible = isoComp-cong (T.idIso b) (T.postWhisker-idIso (W.map (G.projection B)) (Q.pair B)) then
          isoComp-unitʳ-at b then (cancel-right d b) ⁻¹ then
          isoComp-cong matching-computation (T.idIso (d ⁻¹)) then
          isoComp-assoc-at (G.generic ◁ ε) M (d ⁻¹) }

  square-isPullback : IsPullback square
  square-isPullback = pullback-cone-invariant (coneSwap-swap square)
    (pullback-swap (coneSwap square)
      (Paste.cancel-isPullback (coneSwap square)
        (ArrowChange.ChangeLeft.reflect T PT δ G.generic outer
          (pullback-cone-invariant (coneIso-inverse recovery-comparison)
            (pullback-swap (F.recovery-cone B) (R.local-isEquiv B))))))

  reflects-equivalence : S.IsEquiv (QA.Σ-map f) → T.IsEquiv f
  reflects-equivalence h = PullbackEquivalences.degenerate-pullback-converse T PT
    (Core.Results.preservesEquiv W h) square square-isPullback
```
