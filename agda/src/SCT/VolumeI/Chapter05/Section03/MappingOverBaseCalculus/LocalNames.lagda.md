# The local mapping comparison on names

The cone comparison below retains the matching obtained from the original
mapping-over-base construction. Its two legs are then normalized to the
name of the dependent sum and the identity of the terminal category.

The cone `normalized` retains that transported matching; `simple` uses
the original projection-naturality triangle. Their matching comparison
is not asserted here. A proof by family restriction needs the computation
`restrict-cong (reflect alpha) = alpha` for `SumFamilies.reflect`, and
reflection of identifications between restricted identifications.
These are proof obligations, not additional hypotheses.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.MappingPullbacks as MapPullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackFunctor as PullbackFunctor
import SCT.VolumeI.Chapter01.Section06.Cospans.EquivalentCospanCone as Cospans
import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry as Symmetry
import SCT.VolumeI.Chapter03.RelativeCategories.Functors as Relative
import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.MappingFibers as RelativeMapping
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.ProductPullbacks as ProductPullbacks
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.ProductNames as Names
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction
import SCT.VolumeI.Chapter05.Section02.SumMapping as SumMapping
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumMappingNaturality as Naturality
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumMappingPoints as Points
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Generic
import SCT.VolumeI.Chapter05.Section03.GenericFiber as Fiber
import SCT.VolumeI.Chapter05.Section03.Recovery as Recovery
import SCT.VolumeI.Chapter05.Section03.OverBaseCalculus as OverBase

module SCT.VolumeI.Chapter05.Section03.MappingOverBaseCalculus.LocalNames
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (WP : WeakProducts.PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT)
  (FC : Preservation.FunctorComparison W MS MT FS FT)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (PS : Pullbacks.PullbackStructure S) (PT : Pullbacks.PullbackStructure T)
  (R : Recovery.Recovery W P Q A e (Pullbacks.PullbackStructure.dataPullback PT))
  (B C : View.CAT T) where

private
  module S = View S
  module T = View T
module P = Products.DependentProducts P
module Q = Sums.DependentSums Q
module SM = Setup S MS
module N = Names W MT P using (name; post; terminal-isEquiv)
module QA = SumAction W P Q using (Σ-map)
module G = Generic W P Q A e using (base; projection; projection-natural)

import SCT.VolumeI.Chapter05.Section03.LocalMappingOverBase as Local
module L = Local W K WP MS MT FS FT FC P Q A e PS PT R B C
  using (cospan; point-target; post-target; fiber-comparison;
    module LocalPullback; module Changed; module Point)
module Changed = L.Changed using (factor; factor-cone)
open Pullbacks.PullbackStructure PS
import SCT.VolumeI.Chapter01.Section06.PullbackSquares as Squares
open Squares S PS
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry S
  using (coneSwap; coneIso-swap; coneSwap-pre)
import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction as CospanAction
module Change = PullbackFunctor.CospanMap L.cospan using (mapCone; right)
module ChangeCones = CospanAction.Action S PS L.cospan using (map-pre)
module Sym = Symmetry S PS using (pullbackSwap)
module Point (D : S.CAT) = Points W WP MS MT FS FT FC P Q B D
  using (comparison-name)
open S using (_∘_; _◁_; _∙_; _⁻¹)

target : Cone L.post-target L.point-target (Pullback L.post-target L.point-target)
target = pullbackCone L.post-target L.point-target

transported : (f : T.MAP B C) → Cone L.post-target L.point-target S.One
transported f = coneSwap (Change.mapCone (conePre (N.name f) L.LocalPullback.square))

module SwapFactor {X Y Z H : S.CAT} (u : S.MAP X Z) (v : S.MAP Y Z)
  (m : S.MAP H (Pullback u v)) (s : Cone u v H)
  (Φ : ConeIso (conePre m (pullbackCone u v)) s) where

  opaque
    reassociate : ConeIso
      (conePre (Sym.pullbackSwap u v ∘ m) (pullbackCone v u))
      (conePre m (conePre (Sym.pullbackSwap u v) (pullbackCone v u)))
    reassociate = coneIso-inverse (conePre-assoc m (Sym.pullbackSwap u v) (pullbackCone v u))

    swap-computation : ConeIso
      (conePre m (conePre (Sym.pullbackSwap u v) (pullbackCone v u)))
      (conePre m (coneSwap (pullbackCone u v)))
    swap-computation = coneIso-pre m (pullbackLift-β (coneSwap (pullbackCone u v)))

    restrict-swap : ConeIso
      (conePre m (coneSwap (pullbackCone u v)))
      (coneSwap (conePre m (pullbackCone u v)))
    restrict-swap = coneSwap-pre m (pullbackCone u v)

    swap-original : ConeIso (coneSwap (conePre m (pullbackCone u v))) (coneSwap s)
    swap-original = coneIso-swap Φ

    comparison : ConeIso
      (conePre (Sym.pullbackSwap u v ∘ m) (pullbackCone v u)) (coneSwap s)
    comparison = coneIso-compose swap-original
      (coneIso-compose restrict-swap (coneIso-compose swap-computation reassociate))
opaque
  factor-comparison : ConeIso (conePre L.fiber-comparison target)
    (coneSwap (Change.mapCone L.LocalPullback.square))
  factor-comparison = SwapFactor.comparison L.point-target L.post-target
    Changed.factor (Change.mapCone L.LocalPullback.square) Changed.factor-cone
  comparison : (f : T.MAP B C) → ConeIso
    (conePre (L.fiber-comparison ∘ N.name f) target) (transported f)
  comparison f = coneIso-compose
    (coneIso-swap (coneIso-inverse (ChangeCones.map-pre (N.name f) L.LocalPullback.square)))
    (coneIso-compose
      (coneSwap-pre (N.name f) (Change.mapCone L.LocalPullback.square))
      (coneIso-compose (coneIso-pre (N.name f) factor-comparison)
        (coneIso-inverse (conePre-assoc (N.name f) L.fiber-comparison target))))

  left-comparison : (f : T.MAP B C) → S._=₁_
    (Cone.left (transported f)) (SM.nameMap (QA.Σ-map f))
  left-comparison f = L.Point.comparison-name (Q.Σ C) (T._∘_ (Q.pair C) f) ∙
    (Change.right ◁ N.post (Q.pair C) f)

normalized : (f : T.MAP B C) → Cone L.post-target L.point-target S.One
normalized f = coneRetarget (transported f) (SM.nameMap (QA.Σ-map f)) (S.id S.One)
  (left-comparison f) (S.terminal-iso _ _)

opaque
  normalized-comparison : (f : T.MAP B C) → ConeIso
    (conePre (L.fiber-comparison ∘ N.name f) target) (normalized f)
  normalized-comparison f = coneIso-compose
    (coneRetarget-β (transported f) (SM.nameMap (QA.Σ-map f)) (S.id S.One)
      (left-comparison f) (S.terminal-iso _ _)) (comparison f)

simple : (f : T.MAP B C) → Cone L.post-target L.point-target S.One
simple f = record
  { left = SM.nameMap (QA.Σ-map f)
  ; right = S.id S.One
  ; match = (S.comp-unitʳ L.point-target) ⁻¹ ∙
      (SM.nameMapIso (G.projection-natural f) ∙ SM.mapPost-name (G.projection C) (QA.Σ-map f)) }

import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductCones as ProductCones
import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeUncurrying as MappingCones
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction as ConeAction
module W = Weakening W
module TM = Setup T MT
module TC = Pullbacks.PullbackStructure PT
module TS = Squares T PT
module F = Fiber W P Q A e TC.dataPullback using (recovery-cone)
module RA = Recovery.Recovery R
module MP = MapPullbacks T MT PT using (mappedCone; map-preserves-pullback; module MappedCone)
module ProductImage = L.LocalPullback using (evaluation-comparison)
module ProductCone = ProductCones W K P using (uncurryCone)
module MappingCone = MappingCones T MT using (uncurryCone; uncurryConeIso)

local-evaluation : (f : T.MAP B C) → T._=₁_
  (TM.mapUncurry (P.uncurry (N.name f)))
  (T._∘_ f (T.pr₂ {W.cat S.One} {B}))
local-evaluation f = Calculus._then_ T
  (TM.mapUncurry-cong (T._⁻¹ (P.curry-β (T._∘_ (TM.nameMap f) (T.terminate (W.cat S.One))))))
  (Calculus._then_ T
    (TM.mapUncurry-restrict (TM.nameMap f) (T.terminate (W.cat S.One)))
    (Calculus._then_ T
      (T._▷_ (TM.mapCurry-β T.one-isAn (T._∘_ f T.pr₂))
        (TM.productMap (T.terminate (W.cat S.One)) (T.id B)))
      (Calculus._then_ T
        (T.comp-assoc (TM.productMap (T.terminate (W.cat S.One)) (T.id B)) T.pr₂ f)
        (T._◁_ f (Calculus._then_ T (T.pair-β₂ _ _) (T.comp-unitˡ T.pr₂))))))

opaque
  source-evaluation : (f : T.MAP B C) → TS.ConeIso
    (MappingCone.uncurryCone
      (ProductCone.uncurryCone (conePre (N.name f) L.LocalPullback.square)))
    (TS.conePre (T._∘_ f (T.pr₂ {W.cat S.One} {B})) (F.recovery-cone C))
  source-evaluation f = TS.coneIso-compose
    (ConeAction.cone-action T (F.recovery-cone C) (local-evaluation f))
    (TS.coneIso-compose
      (MP.MappedCone.evaluate B (F.recovery-cone C) (P.uncurry (N.name f)))
      (MappingCone.uncurryConeIso (ProductImage.evaluation-comparison (N.name f))))
```