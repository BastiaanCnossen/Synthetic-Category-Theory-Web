# Pullbacks of total categories

The pair cospan sends a local pullback to a square cartesian over its
left leg. Pasting with recovery gives a generic-point pullback square.
Recovery then proves that extension of its right leg is an equivalence
onto the absolute pullback.

The total cone is first obtained by extension of the whole pair cone,
as in `SumCones`. The matching comparison then identifies it with the
cone formed using the specified sum compositor and sum congruence.
Both whole cones are proved to be pullbacks.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ConeTransport as Transport
import SCT.VolumeI.Chapter05.Section01.PullbackPreservation as WeakPullbacks
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.SumCones as SumCones
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumConeMatching as Matching
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point
import SCT.VolumeI.Chapter05.Section03.GenericFiber as Fiber
import SCT.VolumeI.Chapter05.Section03.Recovery as Recovery
import SCT.VolumeI.Chapter05.Section03.RecoverEquivalence as Detection
import SCT.VolumeI.Chapter05.Section03.PairPullbacks as Pairs
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackSquares as Squares
import SCT.VolumeI.Chapter01.Section06.PullbackFunctor as Functor
import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry as Symmetry
import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange as ArrowChange
import SCT.VolumeI.Chapter01.Section06.PastingLemma as Pasting
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks as Cartesian
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting as ConePasting
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange as ConeChange
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction as ConeAction
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing

module SCT.VolumeI.Chapter05.Section03.SumPullbacks
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W)
  (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (PS : Pullbacks.PullbackStructure S) (PT : Pullbacks.PullbackStructure T)
  (WP : WeakPullbacks.PreservesPullbacks W (Pullbacks.PullbackStructure.dataPullback PS)
    (Pullbacks.PullbackStructure.dataPullback PT))
  (R : Recovery.Recovery W P Q A e (Pullbacks.PullbackStructure.dataPullback PT)) where

private
  module S = View S
  module T = View T
module W = Weakening W
module Q = Sums.DependentSums Q
module QA = Action W P Q using (Σ-map)
module SC = Squares S PS
module TC = Squares T PT
module PS = Pullbacks.PullbackStructure PS
module G = Point W P Q A e using (base; generic; projection)
module F = Fiber W P Q A e (Pullbacks.PullbackStructure.dataPullback PT) using (recovery-cone)
module R = Recovery.Recovery R
module CT = Transport W K using (cone; restrict)
module CS = SumCones W K P Q using (restrictCone; module Reflection; module RestrictionComparison; module Total)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open TC using (Cone; ConeIso; IsPullback; coneIso-compose; coneIso-inverse; coneIso-pre;
  conePre; conePre-assoc; pullback-cone-invariant)
open ConeChange T using (coneSwap; changeLeft)
open Symmetry T PT using (pullback-swap)
open Functor T PT using (CospanMap)
open ConePasting T using (compositeCone-compatible)
open Pairing T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (cancel-right)

-- The cartesian-cospan calculation with an arbitrary universal target cone.
module CartesianTarget {B C D B′ C′ D′ Z Y : T.CAT}
  {f : T.MAP B D} {g : T.MAP C D} {f′ : T.MAP B′ D′} {g′ : T.MAP C′ D′}
  (M : CospanMap f g f′ g′)
  (right-pullback : IsPullback (Cartesian.rightSquareOf T PT M))
  (source : Cone f g Z) (source-isPullback : IsPullback source)
  (target : Cone f′ g′ Y) (target-isPullback : IsPullback target) where

  open CospanMap M using (mapCone) renaming (left to u)
  module Known = Cartesian.Mapped T PT M right-pullback source source-isPullback
    using (outerMapped; outer-isPullback)
  module U = TC.UniversalCone target target-isPullback using (factor; factor-β)
  p = Cone.left source
  H = U.factor (mapCone source)
  full-β = U.factor-β (mapCone source)
  legLeft = ConeIso.leftIso full-β
  ρ = ConeIso.rightIso full-β
  σ = Cone.match (mapCone source)

  square : Cone u (Cone.left target) Z
  square = record { left = p ; right = H ; match = legLeft ⁻¹ }
  module Paste = Pasting.Pasting T PT u f′ g′ target target-isPullback
    using (module Paste; cancel-isPullback)

  outer-comparison : ConeIso (Paste.Paste.flatten square) Known.outerMapped
  outer-comparison = compositeCone-compatible u f′ _ _ (T.idIso p) ρ
    (isoComp-cong (T.idIso (g′ ◁ ρ)) ((Paste.Paste.flatten-match square) ⁻¹) ∙
    (isoComp-assoc-at (g′ ◁ ρ) ν (f′ ◁ legLeft ⁻¹) ∙
    (cancel ⁻¹ ∙
    (isoComp-unitʳ-at σ ∙
      isoComp-cong (cancel-right (T.comp-assoc p u f′) σ)
        (T.postWhisker-idIso f′ (u ∘ p) ∙ (T.postWhisker f′ ◁ T.postWhisker-idIso u p))))))
    where
    ν = Cone.match (conePre H target)
    inverseImage = T.postWhisker-idIso f′ (u ∘ p) ∙
      ((T.postWhisker f′ ◁ isoComp-inverseʳ-at legLeft) ∙
        (postWhisker-isoComp-at f′ legLeft (legLeft ⁻¹)) ⁻¹)
    cancel : T._=₂_ (((g′ ◁ ρ) ∙ ν) ∙ (f′ ◁ legLeft ⁻¹)) σ
    cancel = isoComp-unitʳ-at σ ∙
      (isoComp-cong (T.idIso σ) inverseImage ∙
      (isoComp-assoc-at σ (f′ ◁ legLeft) (f′ ◁ legLeft ⁻¹) ∙
        isoComp-cong ((ConeIso.compatible full-β) ⁻¹) (T.idIso (f′ ◁ legLeft ⁻¹))))

  square-isPullback : IsPullback square
  square-isPullback = Paste.cancel-isPullback square
    (pullback-cone-invariant (coneIso-inverse outer-comparison) Known.outer-isPullback)

module Preservation {B C D Z : T.CAT} {f : T.MAP B D} {g : T.MAP C D}
  (s : Cone f g Z) (universal : IsPullback s) where

  module Total = CS.Total PT s using (cospan; pairCone; cone; pair-comparison)
  module Pair = Pairs.Naturality W K P Q A e PT R g using (square; square-isPullback)
  target = PS.pullbackCone (QA.Σ-map f) (QA.Σ-map g)
  weakened-target = CT.cone target
  target-isPullback = WeakPullbacks.PreservesPullbacks.comparison-isEquiv WP (QA.Σ-map f) (QA.Σ-map g)
  module Comparison = CartesianTarget Total.cospan (pullback-swap Pair.square Pair.square-isPullback)
    s universal weakened-target target-isPullback
    using (H; full-β; square; square-isPullback)

  total-map = Q.extend Comparison.H
  base-projection = S._∘_ (G.projection B) (SC.Cone.left target)
  recovery = coneSwap (F.recovery-cone B)
  module Paste = Pasting.Pasting T PT (W.map (SC.Cone.left target))
    (W.map (G.projection B)) G.generic recovery
    (pullback-swap (F.recovery-cone B) (R.local-isEquiv B))
    using (module Paste; paste-isPullback)
  outer = Paste.Paste.flatten (coneSwap Comparison.square)
  change = (W.comp (SC.Cone.left target) (G.projection B)) ⁻¹
  generic-square = coneSwap (changeLeft change outer)

  generic-square-isPullback : IsPullback generic-square
  generic-square-isPullback = pullback-swap (changeLeft change outer)
    (ArrowChange.ChangeLeft.preserve T PT change G.generic outer
      (Paste.paste-isPullback (coneSwap Comparison.square)
        (pullback-swap Comparison.square Comparison.square-isPullback)))

  total-map-isEquiv : S.IsEquiv total-map
  total-map-isEquiv = Detection.FromGenericSquare.isEquiv W P Q A e PT R
    base-projection total-map generic-square (Q.extend-β Comparison.H) generic-square-isPullback

  restricted-factor : ConeIso
    (CS.restrictCone (SC.conePre total-map target)) Total.pairCone
  restricted-factor = coneIso-compose Comparison.full-β
    (coneIso-compose (ConeAction.cone-action T weakened-target ((Q.extend-β Comparison.H) ⁻¹))
    (coneIso-compose (conePre-assoc (Q.pair Z) (W.map total-map) weakened-target)
    (coneIso-compose (coneIso-pre (Q.pair Z) (CT.restrict total-map target))
      (CS.RestrictionComparison.comparison (SC.conePre total-map target)))))

  total-comparison : SC.ConeIso (SC.conePre total-map target) Total.cone
  total-comparison = CS.Reflection.comparison _ _
    (coneIso-compose (coneIso-inverse Total.pair-comparison) restricted-factor)

  square : SC.Cone (QA.Σ-map f) (QA.Σ-map g) (Q.Σ Z)
  square = Total.cone

  square-isPullback : SC.IsPullback square
  square-isPullback = SC.pullback-cone-invariant total-comparison
    (SC.pullback-restrict-equivalence target total-map
      (SC.pullbackCone-isPullback (QA.Σ-map f) (QA.Σ-map g)) total-map-isEquiv)

  module Direct = Matching.Matching W K P Q PT s using (cone; comparison)

  direct-square : SC.Cone (QA.Σ-map f) (QA.Σ-map g) (Q.Σ Z)
  direct-square = Direct.cone

  direct-square-isPullback : SC.IsPullback direct-square
  direct-square-isPullback = SC.pullback-cone-invariant Direct.comparison square-isPullback
```
