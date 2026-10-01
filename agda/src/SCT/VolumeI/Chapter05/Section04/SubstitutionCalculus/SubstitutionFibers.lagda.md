# Substitution of a generic fiber

Preserving pullbacks and the generic point identifies the substituted
generic fiber with the fiber over the represented point. The comparison
uses the substitution's terminal equivalence explicitly. This is the
first generic-fiber calculation in the proof of substitution as pullback.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
import SCT.VolumeI.Chapter05.Section01.Routes as Routes
import SCT.VolumeI.Chapter05.Section01.Core as Core
import SCT.VolumeI.Chapter05.Section01.PullbackPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackFunctor as Functor
import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences as Equivalences
import SCT.VolumeI.Chapter01.Section06.Cones as Cones

module SCT.VolumeI.Chapter05.Section04.SubstitutionCalculus.SubstitutionFibers
  {l : Level} {S T U : Theory l l l}
  (W : Weakening S T) (V : Weakening S U) (G : Weakening T U)
  (L : Routes.Comparison (compose G W) V)
  (PT : Pullbacks.PullbackStructure T) (PU : Pullbacks.PullbackStructure U)
  (PG : Preservation.PreservesPullbacks G (Pullbacks.PullbackStructure.dataPullback PT)
    (Pullbacks.PullbackStructure.dataPullback PU))
  (A B : View.CAT S) (g : View.MAP S B A)
  (a : View.MAP T (View.One T) (Weakening.cat W A))
  (b : View.MAP U (View.One U) (Weakening.cat V B))
  (generic : View._=₁_ U
    (View._∘_ U (View.Equiv.functor {T = U} (Routes.Comparison.component L A))
      (View._∘_ U (Weakening.map G a) (Weakening.back G)))
    (View._∘_ U (Weakening.map V g) b)) where

private
  module S = View S
  module T = View T
  module U = View U
module W = Weakening W
module V = Weakening V
module G = Weakening G
module L = Routes.Comparison L
module PT = Pullbacks.PullbackStructure PT
module PU = Pullbacks.PullbackStructure PU
module Transport = Preservation G PT.dataPullback PU.dataPullback
open Functor U PU using (CospanMap)
open U using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus U using (_then_)

λ→ : (X : S.CAT) → U.MAP (G.cat (W.cat X)) (V.cat X)
λ→ X = U.Equiv.functor (L.component X)

terminal→ : U.MAP (G.cat T.One) U.One
terminal→ = U.Equiv.functor G.terminal

generic-square : U._=₁_ ((V.map g ∘ b) ∘ terminal→) (λ→ A ∘ G.map a)
generic-square = (generic ⁻¹ ▷ terminal→) then
  U.comp-assoc terminal→ (G.map a ∘ G.back) (λ→ A) then
  (λ→ A ◁ U.comp-assoc terminal→ G.back (G.map a)) then
  (λ→ A ◁ (G.map a ◁ (U.IsEquiv.sectionIso (U.Equiv.isEquiv G.terminal)) ⁻¹)) then
  (λ→ A ◁ U.comp-unitʳ (G.map a))

module Fiber {X : S.CAT} (p : S.MAP X A) where
  cospan : CospanMap (G.map a) (G.map (W.map p)) (V.map g ∘ b) (V.map p)
  cospan = record
    { left = terminal→ ; right = λ→ X ; base = λ→ A
    ; leftSquare = generic-square ; rightSquare = (L.naturality p) ⁻¹ }

  comparison : U.MAP (G.cat (PT.Pullback a (W.map p))) (PU.Pullback (V.map g ∘ b) (V.map p))
  comparison = CospanMap.pullbackMap cospan ∘ Transport.comparison a (W.map p)

  opaque
    comparison-isEquiv : U.IsEquiv comparison
    comparison-isEquiv = U.equiv-compose (Transport.comparison a (W.map p)) (CospanMap.pullbackMap cospan)
      (Transport.PreservesPullbacks.comparison-isEquiv PG a (W.map p))
      (Equivalences.CospanEquivalence.pullbackMap-isEquiv U PU cospan
        (U.Equiv.isEquiv G.terminal) (U.Equiv.isEquiv (L.component X)) (U.Equiv.isEquiv (L.component A)))

  inclusion : U._=₁_ (PU.pullback₂ ∘ comparison) (λ→ X ∘ G.map (PT.pullback₂ {f = a} {W.map p}))
  inclusion = (U.comp-assoc (Transport.comparison a (W.map p)) (CospanMap.pullbackMap cospan) PU.pullback₂) ⁻¹ then
    (PU.pullbackLift-β₂ (CospanMap.mapCone cospan (PU.pullbackCone (G.map a) (G.map (W.map p))))
      ▷ Transport.comparison a (W.map p)) then
    U.comp-assoc (Transport.comparison a (W.map p)) PU.pullback₂ (λ→ X) then
    (λ→ X ◁ PU.pullbackLift-β₂ (Transport.cone (PT.pullbackCone a (W.map p))))

  module Recovery {C : T.CAT} (s : Cones.Cone T a (W.map p) C)
    (recovery : T.IsEquiv (PT.pullbackLift s)) where

    substituted : U.MAP (G.cat C) (PU.Pullback (V.map g ∘ b) (V.map p))
    substituted = comparison ∘ G.map (PT.pullbackLift s)

    opaque
      substituted-isEquiv : U.IsEquiv substituted
      substituted-isEquiv = U.equiv-compose (G.map (PT.pullbackLift s)) comparison
        (Core.Results.preservesEquiv G recovery) comparison-isEquiv

    pair-comparison : U._=₁_ (PU.pullback₂ ∘ substituted) (λ→ X ∘ G.map (Cones.Cone.right s))
    pair-comparison = (U.comp-assoc (G.map (PT.pullbackLift s)) comparison PU.pullback₂) ⁻¹ then
      (inclusion ▷ G.map (PT.pullbackLift s)) then
      U.comp-assoc (G.map (PT.pullbackLift s)) (G.map PT.pullback₂) (λ→ X) then
      (λ→ X ◁ ((G.comp (PT.pullbackLift s) PT.pullback₂) ⁻¹)) then
      (λ→ X ◁ G.term (PT.pullbackLift-β₂ s))
```
