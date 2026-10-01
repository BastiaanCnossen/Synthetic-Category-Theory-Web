# Substitution and total categories

The two generic-fiber comparisons identify the substituted category
with the generic fiber of the absolute pullback. Taking its dependent
sum and applying total recovery gives the equivalence. Naturality of
the total projection supplies the triangle over the new base.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Contexts
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.Changes as Changes
import SCT.VolumeI.Chapter05.Theory as ContextTheory
import SCT.VolumeI.Chapter05.PullbackChanges as PullbackChanges
import SCT.VolumeI.Chapter05.Section04.Substitution as Substitution
import SCT.VolumeI.Chapter05.Section04.SubstitutionCalculus.SubstitutionFibers as SubstitutionFibers
import SCT.VolumeI.Chapter05.Section04.SubstitutionCalculus.PullbackFibers as PullbackFibers
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point
import SCT.VolumeI.Chapter05.Section03.GenericFiber as Fiber
import SCT.VolumeI.Chapter05.Section03.Recovery as Recovery
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction
import SCT.VolumeI.Chapter05.Section02.DependentEquivalences as Equivalences
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.RelativeCategories.Equivalences as Relative

module SCT.VolumeI.Chapter05.Section04.SubstitutionTotals
  {l : Level} (C : ContextualTheories l) (D : Changes.Changes C)
  (K : ContextTheory.ContextualConstructions C D)
  (PP : PullbackChanges.Preservation C D K) (Γ : ContextualTheories.Context C)
  (R : Substitution.At.Substitution C D K Γ)
  (GR : Substitution.At.GenericCompatibility C D K Γ R)
  (A B : ContextualTheories.In.AN C Γ)
  (g : ContextualTheories.In.MAP C Γ
    (View.AN.category {T = ContextualTheories.at C Γ} B) (View.AN.category {T = ContextualTheories.at C Γ} A))
  (X : ContextualTheories.In.CAT C (ContextualTheories.extend C Γ A)) where

open ContextualTheories C
open Changes.Changes D using (underlying; weakening)
open ContextTheory C D using (W)
open ContextTheory.ContextualConstructions K
module R = Substitution.At.Substitution R
private
  module S = View (at Γ)
  module T = View (Local Γ A)
  module U = View (Local Γ B)
module G = Weakening (R.pull {A} {B} g)
module PS = Pullbacks.PullbackStructure (pullbacks Γ)
module PT = Pullbacks.PullbackStructure (pullbacks (extend Γ A))
module PU = Pullbacks.PullbackStructure (pullbacks (extend Γ B))
module APoint = Point (W Γ A) (dependentProducts Γ A) (dependentSums Γ A) A (terminalSum Γ A)
  using (generic; projection)
module BPoint = Point (W Γ B) (dependentProducts Γ B) (dependentSums Γ B) B (terminalSum Γ B)
  using (generic; projection; projection-natural)
module AFiber = Fiber (W Γ A) (dependentProducts Γ A) (dependentSums Γ A) A (terminalSum Γ A) PT.dataPullback
  using (recovery-cone)
module BFiber = Fiber (W Γ B) (dependentProducts Γ B) (dependentSums Γ B) B (terminalSum Γ B) PU.dataPullback
  using (Fiber; total-recovery; total-recovery-over)
module AR = Recovery.Recovery (recovery Γ A) using (local-isEquiv)
module BR = Recovery.Recovery (recovery Γ B) using (total-isEquiv)
module ΣB = Sums.DependentSums (dependentSums Γ B) using (Σ)
module ΣAction = SumAction (W Γ B) (dependentProducts Γ B) (dependentSums Γ B) using (Σ-map)
module ΣEquiv = Equivalences.SumResults (W Γ B) (dependentProducts Γ B) (dependentSums Γ B)
  using (Σ-map-isEquiv)

module Substituted = SubstitutionFibers (W Γ A) (W Γ B) (R.pull {A} {B} g)
  (R.constant {A} {B} g) (pullbacks (extend Γ A)) (pullbacks (extend Γ B))
  (PP {extend Γ A} {extend Γ B} (R.substitute {A} {B} g))
  (S.AN.category A) (S.AN.category B) g APoint.generic BPoint.generic
  (Substitution.At.GenericCompatibility.generic-point GR {A} {B} g)
  using (module Fiber)
module LocalComparison = Substituted.Fiber.Recovery (APoint.projection X)
  (AFiber.recovery-cone X) (AR.local-isEquiv X) using (substituted; substituted-isEquiv)
module PullbackComparison = PullbackFibers (W Γ B) (pullbacks Γ) (pullbacks (extend Γ B))
  (PP {Γ} {extend Γ B} (weakening Γ B))
  g (APoint.projection X) BPoint.generic using (comparison; comparison-isEquiv)

Total : S.CAT
Total = PS.Pullback g (APoint.projection X)

projection : S.MAP Total (S.AN.category B)
projection = PS.pullback₁

local-comparison : U.MAP (G.cat X) (BFiber.Fiber projection)
local-comparison = U._∘_ (U.IsEquiv.inverse PullbackComparison.comparison-isEquiv) LocalComparison.substituted

opaque
  local-comparison-isEquiv : U.IsEquiv local-comparison
  local-comparison-isEquiv = U.equiv-compose LocalComparison.substituted
    (U.IsEquiv.inverse PullbackComparison.comparison-isEquiv) LocalComparison.substituted-isEquiv
    (U.equiv-inverse PullbackComparison.comparison-isEquiv)

comparison : S.MAP (ΣB.Σ (G.cat X)) Total
comparison = S._∘_ (BFiber.total-recovery projection) (ΣAction.Σ-map local-comparison)

opaque
  comparison-isEquiv : S.IsEquiv comparison
  comparison-isEquiv = S.equiv-compose (ΣAction.Σ-map local-comparison) (BFiber.total-recovery projection)
    (ΣEquiv.Σ-map-isEquiv local-comparison-isEquiv) (BR.total-isEquiv projection)

open S using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus (at Γ) using (_then_)

over-base : S._=₁_ (projection ∘ comparison) (BPoint.projection (G.cat X))
over-base = (S.comp-assoc (ΣAction.Σ-map local-comparison) (BFiber.total-recovery projection) projection) ⁻¹ then
  (BFiber.total-recovery-over projection ▷ ΣAction.Σ-map local-comparison) then
  BPoint.projection-natural local-comparison

functor-over-base : S.FunctorLift projection (BPoint.projection (G.cat X))
functor-over-base = record { lift = comparison ; comparison = over-base }

module OverBase = Relative.Inverse (at Γ) (mapping Γ) (functors Γ) (pullbacks Γ)
  functor-over-base comparison-isEquiv using (inverse; left-inverse; right-inverse)
```
