# Local mapping animae and functors over the base

Apply mapping animae and dependent products to the recovery square.
The sum mapping equivalence and its naturality identify the resulting
cospan with postcomposition over the total base. This constructs an
equivalence of whole animae, retaining the matching of the pullback.
Its underlying functor is computed on named local functors below. The
identification of its triangle over the base with the separately chosen
projection-naturality witness remains to be proved.

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

module SCT.VolumeI.Chapter05.Section03.LocalMappingOverBase
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
module W = Weakening W
module P = Products.DependentProducts P
module Q = Sums.DependentSums Q
module SM = Setup S MS
  using (Map; mapPost; nameMap; nameMapIso)
module TM = Setup T MT
  using (Map; mapPost)
module PA = Action W P using (Π-map)
module QA = SumAction W P Q using (extend-cong; extend-η; Σ-map)
module N = Names W MT P using (name; post; terminal-isEquiv)
module G = Generic W P Q A e using (base; generic; projection; projection-β)
module F = Fiber W P Q A e (Pullbacks.PullbackStructure.dataPullback PT) using (recovery-cone)
module R = Recovery.Recovery R
module Sum (D : S.CAT) = SumMapping W WP MS MT FS FT FC P Q B D using (module Result)
module Point (D : S.CAT) = Points W WP MS MT FS FT FC P Q B D using (comparison-name)
module MP = MapPullbacks T MT PT using (mappedCone; map-preserves-pullback)
module LocalPullback = ProductPullbacks.Preservation W K P PS PT
  (MP.mappedCone B (F.recovery-cone C))
  (MP.map-preserves-pullback B (F.recovery-cone C) (R.local-isEquiv C))
  using (square; square-isPullback; evaluation-comparison)
module PS = Pullbacks.PullbackStructure PS
module Projections = OverBase.PullbackProjections S PS using (swap-first-after)
module Sym = Symmetry S PS using (pullbackSwap; pullbackSwap-isEquiv)
module RM = RelativeMapping.MappingFiber S MS FS PS (G.projection B) (G.projection C)
  using (comparison; comparison-isEquiv; forget; forget-comparison)
open PullbackFunctor S PS using (CospanMap)
open S using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus S using (_then_)

terminal-source = P.Π (TM.Map B T.One)
terminal-point = N.name (T.terminate B)
point-target = SM.nameMap (G.projection B)
post-target = SM.mapPost {C = Q.Σ B} (G.projection C)
base-change = Sum.Result.G G.base
source-left = PA.Π-map (TM.mapPost {C = B} G.generic)

projection-extension : S._=₁_ (Q.extend (T._∘_ G.generic (T.terminate B))) (G.projection B)
projection-extension = QA.extend-cong (T._⁻¹ (G.projection-β B)) then QA.extend-η (G.projection B)

point-comparison : S._=₁_ ((base-change ∘ source-left) ∘ terminal-point) point-target
point-comparison = S.comp-assoc terminal-point source-left base-change then
  (base-change ◁ N.post G.generic (T.terminate B)) then
  Point.comparison-name G.base (T._∘_ G.generic (T.terminate B)) then
  SM.nameMapIso projection-extension

terminal-square : S._=₁_ (point-target ∘ S.terminate terminal-source) (base-change ∘ source-left)
terminal-square = (S.comp-unitʳ (base-change ∘ source-left) ⁻¹ then
  ((base-change ∘ source-left) ◁ S.IsEquiv.sectionIso (N.terminal-isEquiv B)) then
  (S.comp-assoc (S.terminate terminal-source) terminal-point (base-change ∘ source-left)) ⁻¹ then
  (point-comparison ▷ S.terminate terminal-source)) ⁻¹

cospan : CospanMap source-left (PA.Π-map (TM.mapPost (W.map (G.projection C)))) point-target post-target
cospan = record
  { left = S.terminate terminal-source ; right = Sum.Result.G (Q.Σ C) ; base = base-change
  ; leftSquare = terminal-square
  ; rightSquare = (Naturality.comparison W WP MS MT FS FT FC P Q B (G.projection C)) ⁻¹ }

module Changed = Cospans.Transport S PS cospan (N.terminal-isEquiv B)
  (S.equiv-inverse (Sum.Result.isEquiv (Q.Σ C))) (S.equiv-inverse (Sum.Result.isEquiv G.base))
  LocalPullback.square LocalPullback.square-isPullback
  using (factor; factor-isEquiv; factor-cone; left-comparison; right-comparison)

fiber-comparison : S.MAP (P.Π (TM.Map B C)) (PS.Pullback post-target point-target)
fiber-comparison = Sym.pullbackSwap point-target post-target ∘ Changed.factor

fiber-comparison-isEquiv : S.IsEquiv fiber-comparison
fiber-comparison-isEquiv = S.equiv-compose Changed.factor (Sym.pullbackSwap point-target post-target)
  Changed.factor-isEquiv (Sym.pullbackSwap-isEquiv point-target post-target)

comparison : S.MAP (P.Π (TM.Map B C)) (Relative.MapOver S MS FS PS (G.projection B) (G.projection C))
comparison = S.IsEquiv.inverse RM.comparison-isEquiv ∘ fiber-comparison

comparison-isEquiv : S.IsEquiv comparison
comparison-isEquiv = S.equiv-compose fiber-comparison (S.IsEquiv.inverse RM.comparison-isEquiv)
  fiber-comparison-isEquiv (S.equiv-inverse RM.comparison-isEquiv)

equivalence : S.Equiv (P.Π (TM.Map B C)) (Relative.MapOver S MS FS PS (G.projection B) (G.projection C))
equivalence = record { functor = comparison ; isEquiv = comparison-isEquiv }

opaque
  underlying-comparison : S._=₁_ (PS.pullback₁ {f = post-target} {g = point-target} ∘ fiber-comparison)
    (Sum.Result.G (Q.Σ C) ∘ PA.Π-map (TM.mapPost (Q.pair C)))
  underlying-comparison = Calculus._then_ S
    {C = P.Π (TM.Map B C)} {D = SM.Map (Q.Σ B) (Q.Σ C)}
    {f = PS.pullback₁ {f = post-target} {g = point-target} ∘ fiber-comparison}
    {g = PS.pullback₂ {f = point-target} {g = post-target} ∘ Changed.factor}
    {h = Sum.Result.G (Q.Σ C) ∘ PA.Π-map (TM.mapPost (Q.pair C))}
    (Projections.swap-first-after {X = P.Π (TM.Map B C)} point-target post-target Changed.factor)
    Changed.right-comparison

  underlying-on-name : (f : T.MAP B C)
    → S._=₁_ ((PS.pullback₁ {f = post-target} {g = point-target} ∘ fiber-comparison) ∘ N.name f) (SM.nameMap (QA.Σ-map f))
  underlying-on-name f = (underlying-comparison ▷ N.name f) then
    S.comp-assoc (N.name f) (PA.Π-map (TM.mapPost (Q.pair C))) (Sum.Result.G (Q.Σ C)) then
    (Sum.Result.G (Q.Σ C) ◁ N.post (Q.pair C) f) then
    Point.comparison-name (Q.Σ C) (T._∘_ (Q.pair C) f)

  relative-forget : S._=₁_ (RM.forget ∘ S.IsEquiv.inverse RM.comparison-isEquiv)
    (PS.pullback₁ {f = post-target} {g = point-target})
  relative-forget = ((RM.forget-comparison) ⁻¹ ▷ S.IsEquiv.inverse RM.comparison-isEquiv) then
    S.comp-assoc (S.IsEquiv.inverse RM.comparison-isEquiv) RM.comparison (PS.pullback₁ {f = post-target} {g = point-target}) then
    (PS.pullback₁ {f = post-target} {g = point-target} ◁ (S.IsEquiv.retractionIso RM.comparison-isEquiv) ⁻¹) then
    S.comp-unitʳ (PS.pullback₁ {f = post-target} {g = point-target})

  forget-on-name : (f : T.MAP B C)
    → S._=₁_ ((RM.forget ∘ comparison) ∘ N.name f) (SM.nameMap (QA.Σ-map f))
  forget-on-name f =
    ((S.comp-assoc fiber-comparison (S.IsEquiv.inverse RM.comparison-isEquiv) RM.forget) ⁻¹ ▷ N.name f) then
    ((relative-forget ▷ fiber-comparison) ▷ N.name f) then underlying-on-name f
```
