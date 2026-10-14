# Retracts of functors

A retract consists of a square into the larger functor, a square back,
and a specified identification of their composite with the identity square.
`SquareEquality` includes both endpoint retractions and their compatibility.
The comparison with the loop formulation of the first rebuild is in
RetractLoops.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Retracts where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; postWhisker-id₌; module Composition)
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc; comp₌-unitˡ; comp₌-unitʳ; comp₌-inverseˡ; comp₌-inverseʳ;
    inv-comp-left; comp-inv-right; postWhisker-comp₌; post-constant; const-cong; const-One)
open import SCT.VolumeI.Chapter01.Section03.Squares
open Operations
open Composition

module _ {Γ : Context} where
  record Retract {C D C′ D′ : CAT Γ}
    (f : MAP C D) (f′ : MAP C′ D′) : Set m where
    field
      map : Square f f′
      retraction : Square f′ f
      retraction-law : SquareEquality (comp-square retraction map) (id-square f)
```

## The identity retract

Every functor is a retract of itself, by the identity square in both
directions. The required identification of the pasted identity squares with
the identity square is the right unit law of pasting, which rests on Kelly's
lemmas (Section03.Squares, Identifications.FunctorCoherence).

```agda
  identity-retract : {C D : CAT Γ} (f : MAP C D) → Retract f f
  identity-retract f = record
    { map = id-square f
    ; retraction = id-square f
    ; retraction-law = comp-square-unitʳ (id-square f)
    }
```

## Equivalences are closed under retracts

If `u` is the inverse of the larger functor, the inverse of the retract is
obtained by composing the inclusion on its target, `u`, and the retraction
on its source. The two inverse laws follow by pasting the supplied squares
with the endpoint retraction laws. The public hypothesis is the full retract.

```agda
  retract-isEquiv : {C D C′ D′ : CAT Γ} {f : MAP C D} {f′ : MAP C′ D′}
    → Retract f f′ → IsEquiv f′ → IsEquiv f
  retract-isEquiv {C = C} {D = D} {f = f} {f′} R e =
    let inclusion = Retract.map R
        retraction = Retract.retraction R
        law = Retract.retraction-law R
        g = Square.source-map inclusion
        h = Square.source-map retraction
        k = Square.target-map inclusion
        j = Square.target-map retraction
        section-square = Square.cell inclusion
        retraction-square = Square.cell retraction
        source-law = SquareEquality.source-identification law
        target-law = SquareEquality.target-identification law
        u = IsEquiv.inverse e
        w : MAP D C
        w = h ∘ (u ∘ k)
        right : (f ∘ w) =₁ (id D)
        right = target-law ∙ ((j ◁ comp-unitˡ k) ∙
          ((j ◁ ((IsEquiv.right-inverse-law e) ⁻¹ ▷ k)) ∙
          ((j ◁ (comp-assoc k u f′) ⁻¹) ∙
          (comp-assoc (u ∘ k) f′ j ∙ ((retraction-square ▷ (u ∘ k)) ∙
          (comp-assoc (u ∘ k) h f) ⁻¹)))))
        left : (w ∘ f) =₁ (id C)
        left = source-law ∙ ((h ◁ comp-unitˡ g) ∙
          ((h ◁ ((IsEquiv.left-inverse-law e) ⁻¹ ▷ g)) ∙
          ((h ◁ (comp-assoc g f′ u) ⁻¹) ∙
          ((h ◁ (u ◁ section-square ⁻¹)) ∙
          ((h ◁ comp-assoc f k u) ∙ comp-assoc f (u ∘ k) h)))))
    in record { inverse = w ; left-inverse-law = left ⁻¹ ; right-inverse-law = right ⁻¹ }
```
