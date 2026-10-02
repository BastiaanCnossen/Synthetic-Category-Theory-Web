# Calculus of factorizations

A factorization `FunctorLift f d` is a functor `l` together with the specified
identification `f ∘ l ≅ d`. Later sections repeatedly identify, compose, and
restrict such factorizations. The operations below construct the factorization
together with its comparison. Each comparison is the literal pasting that the
earlier hand-written arguments used, so clients obtain the same witnesses.

Uniqueness is stated relative to a reflection of identifications. It
therefore applies both to equivalences (`equiv-reflect`) and to embeddings
(`embedding-reflect`), without importing pullbacks here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence

module SCT.VolumeI.Chapter01.Section03.FactorizationCalculus
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P) where

open Vocabulary V
open Operations V
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open import SCT.VolumeI.Chapter01.Section03.Equivalences V T P PL S using (FunctorLift)
open FunctorLift
```

## Identities, change of target, and restriction

The identity factorization, the transport of a factorization along an
identification of its target, and the restriction of a factorization
along a functor into its source.

```agda
lift-id : {C D : CAT} (f : MAP C D) → FunctorLift f f
lift-id f = record { lift = id _ ; comparison = comp-unitʳ f }

lift-retarget : {C D X : CAT} {f : MAP C D} {d d′ : MAP X D} →
  d =₁ d′ → FunctorLift f d → FunctorLift f d′
lift-retarget α l = record { lift = lift l ; comparison = α ∙ comparison l }

lift-restrict : {C D X Y : CAT} {f : MAP C D} {d : MAP X D} →
  FunctorLift f d → (p : MAP Y X) → FunctorLift f (d ∘ p)
lift-restrict {f = f} l p = record { lift = lift l ∘ p
  ; comparison = (comparison l ▷ p) ∙ (comp-assoc p (lift l) f) ⁻¹ }
```

## Composition

A factorization of `f` through `g` composes with a factorization of `d`
through `f`. The second form composes after postcomposing with `k`: it
factors `k ∘ d` through `n` from a factorization of `k ∘ m` through `n`.
A commuting square supplies the latter, giving transport of a
factorization along a square.

```agda
lift-compose : {B C D X : CAT} {g : MAP B D} {f : MAP C D} {d : MAP X D} →
  FunctorLift g f → FunctorLift f d → FunctorLift g d
lift-compose {g = g} G F = record { lift = lift G ∘ lift F
  ; comparison = comparison F ∙
      ((comparison G ▷ lift F) ∙ (comp-assoc (lift F) (lift G) g) ⁻¹) }

lift-compose-along : {B C D E X : CAT} (k : MAP D E)
  {n : MAP B E} {m : MAP C D} {d : MAP X D} →
  FunctorLift n (k ∘ m) → FunctorLift m d → FunctorLift n (k ∘ d)
lift-compose-along k {n} {m} G F = record { lift = lift G ∘ lift F
  ; comparison = (k ◁ comparison F) ∙
      (comp-assoc (lift F) m k ∙
        ((comparison G ▷ lift F) ∙ (comp-assoc (lift F) (lift G) n) ⁻¹)) }

square-lift : {C C′ D E : CAT} {k : MAP D E} {m : MAP C D}
  {m′ : MAP C′ E} {k′ : MAP C C′} →
  (k ∘ m) =₁ (m′ ∘ k′) → FunctorLift m′ (k ∘ m)
square-lift {k′ = k′} σ = record { lift = k′ ; comparison = σ ⁻¹ }

lift-along-square : {C C′ D E X : CAT} {k : MAP D E} {m : MAP C D}
  {m′ : MAP C′ E} {k′ : MAP C C′} {d : MAP X D} →
  (k ∘ m) =₁ (m′ ∘ k′) → FunctorLift m d → FunctorLift m′ (k ∘ d)
lift-along-square {k = k} σ = lift-compose-along k (square-lift σ)
```

## Inverses

A factorization whose underlying functor is an equivalence is inverted by
the specified inverse of that equivalence.

```agda
lift-inverse : {A B X : CAT} {p : MAP A X} {q : MAP B X}
  (l : FunctorLift q p) → IsEquiv (lift l) → FunctorLift p q
lift-inverse {q = q} l el = record { lift = IsEquiv.inverse el
  ; comparison = comp-unitʳ q ∙
      ((q ◁ (IsEquiv.retractionIso el) ⁻¹) ∙
        (comp-assoc (IsEquiv.inverse el) (lift l) q ∙
          ((comparison l) ⁻¹ ▷ IsEquiv.inverse el))) }
```

## Equivalent sources

If `f ∘ u ≅ g ∘ v` and `u` is an equivalence, then `f` factors through `g`
via `v` and the specified inverse of `u`.

```agda
lift-from-equivalent-source : {X A B Z : CAT}
  (f : MAP A Z) (g : MAP B Z) (u : MAP X A) (v : MAP X B) →
  IsEquiv u → (f ∘ u) =₁ (g ∘ v) → FunctorLift g f
lift-from-equivalent-source f g u v eu β = record { lift = v ∘ IsEquiv.inverse eu
  ; comparison = comp-unitʳ f ∙
      ((f ◁ (IsEquiv.retractionIso eu) ⁻¹) ∙
        (comp-assoc (IsEquiv.inverse eu) u f ∙
          ((β ⁻¹ ▷ IsEquiv.inverse eu) ∙ (comp-assoc (IsEquiv.inverse eu) v g) ⁻¹))) }
```

## Uniqueness

When `f` reflects identifications, two factorizations of the same target
have identified underlying functors.

```agda
lift-unique : {C D X : CAT} {f : MAP C D} {d : MAP X D} →
  ((h k : MAP X C) → (f ∘ h) =₁ (f ∘ k) → h =₁ k) →
  (h k : FunctorLift f d) → lift h =₁ lift k
lift-unique reflect h k = reflect _ _ ((comparison k) ⁻¹ ∙ comparison h)
```
