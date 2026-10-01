# Comparing successive substitutions

Apply substitution as pullback twice. Pulling back the first total
comparison and then pasting identifies the result with substitution
along the composite map. Local recovery gives the category comparison.
This module does not identify the transported coherence witnesses of
the two substitution routes.

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
import SCT.VolumeI.Chapter05.Section04.SubstitutionCalculus.PullbackOverBase as BaseChange
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point
import SCT.VolumeI.Chapter05.Section03.RecoverEquivalence as Recover
import SCT.VolumeI.Chapter05.Section03.OverBaseCalculus as Over
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackSquares as Squares
import SCT.VolumeI.Chapter01.Section06.Pasting.UniversalNestedPullbacks as Nested

module SCT.VolumeI.Chapter05.Section04.SuccessiveSubstitutions
  {l : Level} (C : ContextualTheories l) (D : Changes.Changes C)
  (K : ContextTheory.ContextualConstructions C D)
  (PP : PullbackChanges.Preservation C D K) (Γ : ContextualTheories.Context C)
  (R : Substitution.At.Substitution C D K Γ)
  (GR : Substitution.At.GenericCompatibility C D K Γ R)
  (A B E : ContextualTheories.In.AN C Γ)
  (g : ContextualTheories.In.MAP C Γ
    (View.AN.category {T = ContextualTheories.at C Γ} B) (View.AN.category {T = ContextualTheories.at C Γ} A))
  (h : ContextualTheories.In.MAP C Γ
    (View.AN.category {T = ContextualTheories.at C Γ} E) (View.AN.category {T = ContextualTheories.at C Γ} B))
  (X : ContextualTheories.In.CAT C (ContextualTheories.extend C Γ A)) where

open ContextualTheories C
open ContextTheory C D using (W)
open ContextTheory.ContextualConstructions K
private
  module S = View (at Γ)
  module T = View (Local Γ E)
module R = Substitution.At.Substitution R
module G = Weakening (R.pull {A} {B} g)
module H = Weakening (R.pull {B} {E} h)
module GH = Weakening (R.pull {A} {E} (S._∘_ g h))
module PB = Pullbacks.PullbackStructure (pullbacks Γ)
module APoint = Point (W Γ A) (dependentProducts Γ A) (dependentSums Γ A) A (terminalSum Γ A)
  using (projection)
module EPoint = Point (W Γ E) (dependentProducts Γ E) (dependentSums Γ E) E (terminalSum Γ E)
  using (projection)
module First = Totals C D K PP Γ R GR A B g X
  using (comparison; comparison-isEquiv; functor-over-base)
module Next = Totals C D K PP Γ R GR B E h (G.cat X)
  using (comparison; comparison-isEquiv; functor-over-base)
module Composite = Totals C D K PP Γ R GR A E (S._∘_ g h) X
  using (comparison; comparison-isEquiv; functor-over-base)
module Changed = BaseChange.Along (at Γ) (pullbacks Γ) h First.functor-over-base
  using (map; over; map-isEquiv)
module N = Nested.Nested (at Γ) (pullbacks Γ) h g (APoint.projection X)
  (PB.pullbackCone g (APoint.projection X))
  (Squares.pullbackCone-isPullback (at Γ) (pullbacks Γ) g (APoint.projection X))
  using (flatten; flatten-isEquiv; α)

nested-over : S.FunctorLift (PB.pullback₁ {f = S._∘_ g h} {APoint.projection X})
  (PB.pullback₁ {f = h} {PB.pullback₁ {f = g} {APoint.projection X}})
nested-over = record { lift = N.flatten ; comparison = N.α }

total-functor : S.FunctorLift (EPoint.projection (GH.cat X)) (EPoint.projection (H.cat (G.cat X)))
total-functor = Over.compose (at Γ) (Over.inverse (at Γ) Composite.functor-over-base Composite.comparison-isEquiv)
  (Over.compose (at Γ) nested-over (Over.compose (at Γ) Changed.over Next.functor-over-base))

opaque
  total-isEquiv : S.IsEquiv (S.FunctorLift.lift total-functor)
  total-isEquiv = S.equiv-compose (S._∘_ N.flatten (S._∘_ Changed.map Next.comparison))
    (S.IsEquiv.inverse Composite.comparison-isEquiv)
    (S.equiv-compose (S._∘_ Changed.map Next.comparison) N.flatten
      (S.equiv-compose Next.comparison Changed.map Next.comparison-isEquiv
        (Changed.map-isEquiv First.comparison-isEquiv)) N.flatten-isEquiv)
    (S.equiv-inverse Composite.comparison-isEquiv)

module LocalComparison = Recover.Over (W Γ E) (dependentProducts Γ E) (dependentSums Γ E) E (terminalSum Γ E)
  (pullbacks (extend Γ E)) (recovery Γ E) (H.cat (G.cat X)) (GH.cat X) total-functor total-isEquiv
  using (equivalence)

equivalence : T.Equiv (H.cat (G.cat X)) (GH.cat X)
equivalence = LocalComparison.equivalence
```
