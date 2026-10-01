# Sections of a total category

The absolute anima of objects of the dependent product is equivalent to
the anima of sections of the total projection. First apply the dependent
product mapping equivalence at the terminal category. The terminal
comparison replaces its weakened domain by the local terminal category.
The local mapping equivalence then gives functors over the base, and
restriction along the total projection of the terminal category gives
sections.

A local term also gives a specified section by totalization. The code
constructs both the whole equivalence and this section; their comparison
on named terms still depends on identifying the relative triangle in
LocalMappingOverBase with projection naturality.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.Expressions.RebasedPaths as Rebased
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.RelativeCategories.Functors as Relative
import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Precomposition as Precomposition
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.DependentEquivalences as Equivalences
import SCT.VolumeI.Chapter05.Section02.ProductMapping as ProductMapping
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Generic
import SCT.VolumeI.Chapter05.Section03.Recovery as Recovery
import SCT.VolumeI.Chapter05.Section03.LocalMappingOverBase as LocalMapping

module SCT.VolumeI.Chapter05.Section03.Sections
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (WP : WeakProducts.PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT)
  (FC : Preservation.FunctorComparison W MS MT FS FT)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (PS : Pullbacks.PullbackStructure S) (PT : Pullbacks.PullbackStructure T)
  (R : Recovery.Recovery W P Q A e (Pullbacks.PullbackStructure.dataPullback PT))
  (B : View.CAT T) where

private
  module S = View S
  module T = View T
module W = Weakening W
module P = Products.DependentProducts P
module Q = Sums.DependentSums Q
module SM = Setup S MS
  using (Map)
module TM = Setup T MT
  using (Map; mapPre; mapPre-isEquiv)
module E = Equivalences W P using (Π-equiv)
module SE = Equivalences.SumResults W P Q using (Σ-map-isEquiv)
module QA = SumAction W P Q using (Σ-map)
module G = Generic W P Q A e using (base; projection; projection-natural)
module PM = ProductMapping W WP MS MT P S.One B using (comparison)
module LM = LocalMapping W K WP MS MT FS FT FC P Q A e PS PT R T.One B using (equivalence)
open S using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus S using (_then_)

terminal-projection-isEquiv : S.IsEquiv (G.projection T.One)
terminal-projection-isEquiv = S.equiv-compose (QA.Σ-map (T.terminate T.One)) (S.Equiv.functor e)
  (SE.Σ-map-isEquiv (T.equiv-transport (T.terminal-iso (T.id T.One) (T.terminate T.One)) (T.id-isEquiv T.One)))
  (S.Equiv.isEquiv e)

Sections : S.CAT
Sections = Relative.MapOver S MS FS PS (S.id G.base) (G.projection B)

module Restriction = Precomposition.Precompose S MS FS PS (S.id G.base) (G.projection B)
  (G.projection T.One) (G.projection T.One) (S.comp-unitˡ (G.projection T.One)) using (maps; maps-isEquiv)

terminal-domain : S.Equiv (P.Π (TM.Map (W.cat S.One) B)) (P.Π (TM.Map T.One B))
terminal-domain = E.Π-equiv (record { functor = TM.mapPre W.back
  ; isEquiv = TM.mapPre-isEquiv W.back (T.equiv-inverse (T.Equiv.isEquiv W.terminal)) })

equivalence : S.Equiv (SM.Map S.One (P.Π B)) Sections
equivalence = Rebased.join S PM.comparison (Rebased.join S terminal-domain
  (Rebased.join S LM.equivalence (record
    { functor = S.IsEquiv.inverse (Restriction.maps-isEquiv terminal-projection-isEquiv)
    ; isEquiv = S.equiv-inverse (Restriction.maps-isEquiv terminal-projection-isEquiv) })))

section : (x : T.MAP T.One B) → S.FunctorLift (G.projection B) (S.id G.base)
section x = record
  { lift = QA.Σ-map x ∘ S.IsEquiv.inverse terminal-projection-isEquiv
  ; comparison = (S.comp-assoc (S.IsEquiv.inverse terminal-projection-isEquiv) (QA.Σ-map x) (G.projection B)) ⁻¹ then
      (G.projection-natural x ▷ S.IsEquiv.inverse terminal-projection-isEquiv) then
      (S.IsEquiv.retractionIso terminal-projection-isEquiv) ⁻¹ }
```
