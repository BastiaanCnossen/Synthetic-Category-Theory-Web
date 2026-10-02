# Composing triangles over a base

These operations retain the triangle of a functor over a base. They are
the composition and inverse of factorizations from the Chapter 1
factorization calculus; the inverse triangle uses the selected inverse of
its underlying equivalence.
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
open import SCT.VolumeI.Chapter01.Section03.FactorizationCalculus vocabulary terminal products
  productLaws composition using (lift-compose; lift-inverse)

compose : {A B C X : CAT} {p : MAP A X} {q : MAP B X} {r : MAP C X}
  → FunctorLift r q → FunctorLift q p → FunctorLift r p
compose = lift-compose

inverse : {A B X : CAT} {p : MAP A X} {q : MAP B X}
  (f : FunctorLift q p) → IsEquiv (FunctorLift.lift f) → FunctorLift p q
inverse = lift-inverse

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
