# Identity substitution

The total category of identity substitution is a pullback along the
identity of the base. Its second projection is an equivalence over the
base. Local recovery therefore compares identity substitution with the
original category, without a definitional identity rule for contexts.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Contexts
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.Changes as Changes
import SCT.VolumeI.Chapter05.Theory as ContextTheory
import SCT.VolumeI.Chapter05.PullbackChanges as PullbackChanges
import SCT.VolumeI.Chapter05.Section04.Substitution as Substitution
import SCT.VolumeI.Chapter05.Section04.SubstitutionTotals as Totals
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point
import SCT.VolumeI.Chapter05.Section03.RecoverEquivalence as Recover
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry as Symmetry

module SCT.VolumeI.Chapter05.Section04.IdentitySubstitution
  {l : Level} (C : ContextualTheories l) (D : Changes.Changes C)
  (K : ContextTheory.ContextualConstructions C D)
  (PP : PullbackChanges.Preservation C D K) (Γ : ContextualTheories.Context C)
  (R : Substitution.At.Substitution C D K Γ)
  (GR : Substitution.At.GenericCompatibility C D K Γ R)
  (A : ContextualTheories.In.AN C Γ)
  (X : ContextualTheories.In.CAT C (ContextualTheories.extend C Γ A)) where

open ContextualTheories C
open ContextTheory C D using (W)
open ContextTheory.ContextualConstructions K
private
  module S = View (at Γ)
  module T = View (Local Γ A)
module R = Substitution.At.Substitution R
module Q = Sums.DependentSums (dependentSums Γ A) using (Σ)
module G = Weakening (R.pull {A} {A} (S.id (S.AN.category A)))
module PB = Pullbacks.PullbackStructure (pullbacks Γ)
module GPoint = Point (W Γ A) (dependentProducts Γ A) (dependentSums Γ A) A (terminalSum Γ A)
  using (projection)
module Total = Totals C D K PP Γ R GR A A (S.id (S.AN.category A)) X
  using (comparison; comparison-isEquiv; over-base)
open S using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus (at Γ) using (_then_)

total-comparison : S.MAP (Q.Σ (G.cat X)) (Q.Σ X)
total-comparison = PB.pullback₂ ∘ Total.comparison

opaque
  total-comparison-isEquiv : S.IsEquiv total-comparison
  total-comparison-isEquiv = S.equiv-compose Total.comparison PB.pullback₂ Total.comparison-isEquiv
    (Symmetry.pullback-unitʳ (at Γ) (pullbacks Γ) (GPoint.projection X))

over-base : S._=₁_ (GPoint.projection X ∘ total-comparison) (GPoint.projection (G.cat X))
over-base = (S.comp-assoc Total.comparison PB.pullback₂ (GPoint.projection X)) ⁻¹ then
  ((PB.pullbackMatch ⁻¹ then S.comp-unitˡ PB.pullback₁) ▷ Total.comparison) then Total.over-base

total-functor : S.FunctorLift (GPoint.projection X) (GPoint.projection (G.cat X))
total-functor = record { lift = total-comparison ; comparison = over-base }

module LocalComparison = Recover.Over (W Γ A) (dependentProducts Γ A) (dependentSums Γ A) A (terminalSum Γ A)
  (pullbacks (extend Γ A)) (recovery Γ A) (G.cat X) X total-functor total-comparison-isEquiv
  using (equivalence)

equivalence : T.Equiv (G.cat X) X
equivalence = LocalComparison.equivalence
```

