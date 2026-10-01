# Equivalences and generic fibers

An equivalence over the base induces an equivalence of generic fibers.
Composing it with the two local recovery equivalences compares the
original local categories. The construction uses the specified base
triangle of the given functor.

Conversely, an equivalence on generic fibers implies that the underlying
functor over the base is an equivalence. Naturality of total recovery
follows by restriction along the pair functor; the two recovery maps
then allow cancellation of equivalences.

More generally, a functor out of a total category is an equivalence
when its restriction is the right leg of a generic-point pullback
square. This criterion retains that square's matching and needs no
separately specified triangle for the absolute functor over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction
import SCT.VolumeI.Chapter05.Section02.DependentEquivalences as Equivalences
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point
import SCT.VolumeI.Chapter05.Section03.GenericFiber as Fiber
import SCT.VolumeI.Chapter05.Section03.GenericFiberFunctor as FiberFunctor
import SCT.VolumeI.Chapter05.Section03.Recovery as Recovery
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackSquares as Squares

module SCT.VolumeI.Chapter05.Section03.RecoverEquivalence
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (PB : Pullbacks.PullbackStructure T)
  (R : Recovery.Recovery W P Q A e (Pullbacks.PullbackStructure.dataPullback PB)) where

private
  module S = View S
  module T = View T
module W = Weakening W
module Q = Sums.DependentSums Q
module QA = SumAction W P Q using (Σ-map; reflect; flatten-local-pre; flatten-post)
module QE = Equivalences.SumResults W P Q using (Σ-map-isEquiv)
module G = Point W P Q A e using (base; projection; generic)
module F = Fiber W P Q A e (Pullbacks.PullbackStructure.dataPullback PB)
  using (local-recovery; total-recovery; fiber-inclusion)
module R = Recovery.Recovery R
module TS = Squares T PB using (Cone; IsPullback)
open T using (_◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

module FromGenericSquare {B : T.CAT} {X : S.CAT}
  (p : S.MAP X G.base) (k : S.MAP (Q.Σ B) X)
  (s : TS.Cone G.generic (W.map p) B)
  (right-comparison : T._=₁_ (TS.Cone.right s) (Q.flatten k))
  (universal : TS.IsPullback s) where

  module PB = Pullbacks.PullbackStructure PB

  total-comparison : S._=₁_
    (S._∘_ (F.total-recovery p) (QA.Σ-map (PB.pullbackLift s))) k
  total-comparison = QA.reflect
    (QA.flatten-local-pre (F.total-recovery p) (PB.pullbackLift s) then
      ((Q.extend-β (F.fiber-inclusion p)) ⁻¹ ▷ PB.pullbackLift s) then
      PB.pullbackLift-β₂ s then right-comparison)

  isEquiv : S.IsEquiv k
  isEquiv = S.equiv-transport total-comparison
    (S.equiv-compose (QA.Σ-map (PB.pullbackLift s)) (F.total-recovery p)
      (QE.Σ-map-isEquiv universal) (R.total-isEquiv p))

module Detection {X Y : S.CAT} {p : S.MAP X G.base} {q : S.MAP Y G.base}
  (f : S.FunctorLift q p) where
  module f = S.FunctorLift f
  module Changed = FiberFunctor.Over W P Q A e PB f using (map; inclusion)

  total-recovery-natural : S._=₁_
    (S._∘_ (F.total-recovery q) (QA.Σ-map Changed.map))
    (S._∘_ f.lift (F.total-recovery p))
  total-recovery-natural = QA.reflect
    (QA.flatten-local-pre (F.total-recovery q) Changed.map then
      ((Q.extend-β (F.fiber-inclusion q)) ⁻¹ ▷ Changed.map) then
      Changed.inclusion then
      (W.map f.lift ◁ Q.extend-β (F.fiber-inclusion p)) then
      (QA.flatten-post f.lift (F.total-recovery p)) ⁻¹)

  reflects-equivalence : T.IsEquiv Changed.map → S.IsEquiv f.lift
  reflects-equivalence h = S.equiv-cancel-right (F.total-recovery p) f.lift (R.total-isEquiv p)
    (S.equiv-transport total-recovery-natural
      (S.equiv-compose (QA.Σ-map Changed.map) (F.total-recovery q)
        (QE.Σ-map-isEquiv h) (R.total-isEquiv q)))

module Over (B C : T.CAT) (f : S.FunctorLift (G.projection C) (G.projection B))
  (ef : S.IsEquiv (S.FunctorLift.lift f)) where
  module Changed = FiberFunctor.Over W P Q A e PB f using (map; map-isEquiv)
  inverse-recovery = T.IsEquiv.inverse (R.local-isEquiv C)

  comparison : T.MAP B C
  comparison = T._∘_ inverse-recovery (T._∘_ Changed.map (F.local-recovery B))

  opaque
    comparison-isEquiv : T.IsEquiv comparison
    comparison-isEquiv = T.equiv-compose (T._∘_ Changed.map (F.local-recovery B)) inverse-recovery
      (T.equiv-compose (F.local-recovery B) Changed.map (R.local-isEquiv B) (Changed.map-isEquiv ef))
      (T.equiv-inverse (R.local-isEquiv C))

  equivalence : T.Equiv B C
  equivalence = record { functor = comparison ; isEquiv = comparison-isEquiv }
```
