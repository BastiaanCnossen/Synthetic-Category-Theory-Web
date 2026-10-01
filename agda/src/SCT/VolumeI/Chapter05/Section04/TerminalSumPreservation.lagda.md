# Comparing the sum of the terminal category

The source local terminal category first changes by the terminal
comparison of the lifted operation. Taking its dependent sum and using
the sum-constructor comparison gives the domain comparison for the two
specified equivalences with the base anima. Their chosen inverse data
are compared by the same rule as other equivalence certificates.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
open import SCT.VolumeI.Chapter05.Section01.Products using (PreservesProducts)
import SCT.VolumeI.Chapter05.Section01.Routes as Routes
import SCT.VolumeI.Chapter05.Section01.Expressions.ComparisonObjects as Objects
import SCT.VolumeI.Chapter05.Section01.Expressions.RebasedPaths as Rebased
import SCT.VolumeI.Chapter05.Section01.ComparisonWitnesses as Witnesses
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.DependentEquivalences as Equivalences
import SCT.VolumeI.Chapter05.Section04.DependentPreservation as Preservation

module SCT.VolumeI.Chapter05.Section04.TerminalSumPreservation
  {l : Level} {S T S′ T′ : Theory l l l}
  (W : Weakening S T) (W′ : Weakening S′ T′)
  (U : Weakening S S′) (H : Weakening T T′) (UP : PreservesProducts U)
  (L : Routes.Comparison (compose H W) (compose W′ U))
  (P : Products.DependentProducts W) (P′ : Products.DependentProducts W′)
  (Q : Sums.DependentSums W P) (Q′ : Sums.DependentSums W′ P′)
  (C : Preservation.Sum.SumComparison W W′ U H L P P′ Q Q′)
  (A : View.AN S)
  (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (e′ : View.Equiv S′ (Sums.DependentSums.Σ Q′ (View.One T′))
    (Weakening.cat U (View.AN.category {T = S} A))) where

private
  module S = View S
  module T = View T
  module S′ = View S′
  module T′ = View T′
module U = Weakening U
module H = Weakening H
module Q = Sums.DependentSums Q
module Q′ = Sums.DependentSums Q′
module C = Preservation.Sum.SumComparison C
module O = Objects U UP
module E = Equivalences.SumResults W′ P′ Q′ using (Σ-equiv)

domain : O.Object
domain = record
  { source = Q.Σ T.One ; target = Q′.Σ T′.One
  ; comparison = Rebased.join S′ (C.category T.One) (E.Σ-equiv H.terminal) }

codomain : O.Object
codomain = record
  { source = S.AN.category A ; target = U.cat (S.AN.category A)
  ; comparison = record { functor = S′.id _ ; isEquiv = S′.id-isEquiv _ } }

record Comparison : Set l where
  field
    square : S′._=₁_ (S′._∘_ (O.Object.arrow codomain) (U.map (S.Equiv.functor e)))
      (S′._∘_ (S′.Equiv.functor e′) (O.Object.arrow domain))

  arrow : O.Arrow domain codomain
  arrow = record { source = S.Equiv.functor e ; target = S′.Equiv.functor e′ ; square = square }

  field
    certificate : Witnesses.EquivalenceComparison U UP arrow (S.Equiv.isEquiv e) (S′.Equiv.isEquiv e′)
```
