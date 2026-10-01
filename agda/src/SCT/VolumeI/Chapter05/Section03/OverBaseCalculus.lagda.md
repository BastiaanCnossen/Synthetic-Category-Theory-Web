# Composing triangles over a base

These operations retain the triangle of a functor over a base. The
inverse triangle uses the selected inverse of its underlying equivalence.
The assertion about inverse identifications over the base is supplied
separately by the relative inverse theorem from Chapter 3.

The pullback projection calculation below computes the first projection
after swapping the two legs and restricting along a functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry as Symmetry
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry as ConeSymmetry

module SCT.VolumeI.Chapter05.Section03.OverBaseCalculus {l : Level} (T : Theory l l l) where

open View T
open Calculus T using (_then_)

compose : {A B C X : CAT} {p : MAP A X} {q : MAP B X} {r : MAP C X}
  → FunctorLift r q → FunctorLift q p → FunctorLift r p
compose {r = r} g f = record
  { lift = FunctorLift.lift g ∘ FunctorLift.lift f
  ; comparison = (comp-assoc (FunctorLift.lift f) (FunctorLift.lift g) r) ⁻¹ then
      (FunctorLift.comparison g ▷ FunctorLift.lift f) then FunctorLift.comparison f }

inverse : {A B X : CAT} {p : MAP A X} {q : MAP B X}
  (f : FunctorLift q p) → IsEquiv (FunctorLift.lift f) → FunctorLift p q
inverse {p = p} {q} f ef = record
  { lift = IsEquiv.inverse ef
  ; comparison = ((FunctorLift.comparison f) ⁻¹ ▷ IsEquiv.inverse ef) then
      comp-assoc (IsEquiv.inverse ef) (FunctorLift.lift f) q then
      (q ◁ (IsEquiv.retractionIso ef) ⁻¹) then comp-unitʳ q }

module PullbackProjections (P : Pullbacks.PullbackStructure T) where
  open Pullbacks.PullbackStructure P
  open Symmetry T P using (pullbackSwap)
  open ConeSymmetry T using (coneSwap)

  swap-first-after : {C D E X : CAT} (f : MAP C E) (g : MAP D E)
    (h : MAP X (Pullback f g))
    → (pullback₁ {f = g} {g = f} ∘ (pullbackSwap f g ∘ h)) =₁
        (pullback₂ {f = f} {g = g} ∘ h)
  swap-first-after f g h = (comp-assoc h (pullbackSwap f g) (pullback₁ {f = g} {g = f})) ⁻¹ then
    (pullbackLift-β₁ {f = g} {g = f} (coneSwap (pullbackCone f g)) ▷ h)
```
