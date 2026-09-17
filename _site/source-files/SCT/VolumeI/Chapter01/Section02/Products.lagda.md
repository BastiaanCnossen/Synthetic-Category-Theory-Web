# Products and their functoriality

This module proves the symmetry and unit lemmas and both product exercises
from Section 1.2. All associators and projection comparisons are retained.
The final finite compatibility lemma requires further identifications between
these comparisons; the constructions below do not by themselves assert it.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section02.Products
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P) where

open Vocabulary V
open Operations V
open Terminal.TerminalStructure T
open Terminal.Constructions V T
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Specialization V T P PL S

pair-η : {X C D : CAT} (h : MAP X (C × D))
  → =₁ (pair (pr₁ ∘ h) (pr₂ ∘ h)) h
pair-η h = pair-iso (pair-β₁ (pr₁ ∘ h) (pr₂ ∘ h))
                        (pair-β₂ (pr₁ ∘ h) (pr₂ ∘ h))

pair-projections : {C D : CAT} → =₁ (pair pr₁ pr₂) (id (C × D))
pair-projections = pair-iso
  (invIso (comp-unitʳ pr₁) ∙ pair-β₁ pr₁ pr₂)
  (invIso (comp-unitʳ pr₂) ∙ pair-β₂ pr₁ pr₂)

project-pair₁ : {R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (r : MAP R X)
  → =₁ (pr₁ ∘ (pair f g ∘ r)) (f ∘ r)
project-pair₁ f g r = (pair-β₁ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₁)

project-pair₂ : {R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (r : MAP R X)
  → =₁ (pr₂ ∘ (pair f g ∘ r)) (g ∘ r)
project-pair₂ f g r = (pair-β₂ f g ▷ r) ∙ invIso (comp-assoc r (pair f g) pr₂)
```

The symmetry is its own inverse, with the categories interchanged. Its
two inverse comparisons are the same calculation on different products.

```agda
swap : {C D : CAT} → MAP (C × D) (D × C)
swap = pair pr₂ pr₁

swap-swap : (C D : CAT) → =₁ (swap ∘ swap) (id (C × D))
swap-swap C D = pair-iso
  --! begin swap-swap-first-projection
  (invIso (comp-unitʳ pr₁) ∙ (pair-β₂ pr₂ pr₁ ∙ project-pair₁ pr₂ pr₁ swap))
  --! end swap-swap-first-projection
  --! begin swap-swap-second-projection
  (invIso (comp-unitʳ pr₂) ∙ (pair-β₁ pr₂ pr₁ ∙ project-pair₂ pr₂ pr₁ swap))
  --! end swap-swap-second-projection

swap-isEquiv : (C D : CAT) → IsEquiv (swap {C} {D})
swap-isEquiv C D = record
  { inverse = swap
  ; sectionIso = invIso (swap-swap C D)
  ; retractionIso = invIso (swap-swap D C)
  }

product-unit-inverse : (C : CAT) → MAP C (C × One)
product-unit-inverse C = pair (id C) (terminate C)

product-unit-section : (C : CAT)
  → =₁ (product-unit-inverse C ∘ pr₁) (id (C × One))
product-unit-section C = pair-iso
  --! begin product-unit-first-projection
  (invIso (comp-unitʳ pr₁) ∙
    (comp-unitˡ pr₁ ∙ project-pair₁ (id C) (terminate C) pr₁))
  --! end product-unit-first-projection
  (terminal-iso _ _)

product-unit-isEquiv : (C : CAT) → IsEquiv (pr₁ {C} {One})
product-unit-isEquiv C = record
  { inverse = product-unit-inverse C
  ; sectionIso = invIso (product-unit-section C)
  --! begin product-unit-retraction
  ; retractionIso = invIso (pair-β₁ (id C) (terminate C))
  --! end product-unit-retraction
  }
```

For associativity, each composite is reduced to the original three
projections and then reconstructed using `pair-η`.

```agda
module Associativity (C D E : CAT) where
  forward : MAP ((C × D) × E) (C × (D × E))
  forward = pair (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)

  backward : MAP (C × (D × E)) ((C × D) × E)
  backward = pair (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)

  forward-first : =₁ (pr₁ ∘ forward) (pr₁ ∘ pr₁)
  forward-first = pair-β₁ (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)

  forward-second : =₁ ((pr₁ ∘ pr₂) ∘ forward) (pr₂ ∘ pr₁)
  forward-second = pair-β₁ (pr₂ ∘ pr₁) pr₂ ∙
    ((pr₁ ◁ pair-β₂ (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)) ∙
      comp-assoc forward pr₂ pr₁)

  forward-third : =₁ ((pr₂ ∘ pr₂) ∘ forward) pr₂
  forward-third = pair-β₂ (pr₂ ∘ pr₁) pr₂ ∙
    ((pr₂ ◁ pair-β₂ (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)) ∙
      comp-assoc forward pr₂ pr₂)

  backward-first : =₁ ((pr₁ ∘ pr₁) ∘ backward) pr₁
  backward-first = pair-β₁ pr₁ (pr₁ ∘ pr₂) ∙
    ((pr₁ ◁ pair-β₁ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)) ∙
      comp-assoc backward pr₁ pr₁)

  backward-second : =₁ ((pr₂ ∘ pr₁) ∘ backward) (pr₁ ∘ pr₂)
  backward-second = pair-β₂ pr₁ (pr₁ ∘ pr₂) ∙
    ((pr₂ ◁ pair-β₁ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)) ∙
      comp-assoc backward pr₁ pr₂)

  backward-third : =₁ (pr₂ ∘ backward) (pr₂ ∘ pr₂)
  backward-third = pair-β₂ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)

  backward-forward : =₁ (backward ∘ forward) (id ((C × D) × E))
  backward-forward = pair-projections ∙
    (pair-cong (pair-η pr₁) (idIso pr₂) ∙
      (pair-cong
        (pair-cong forward-first forward-second ∙ pair-pre pr₁ (pr₁ ∘ pr₂) forward)
        forward-third ∙
        pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) forward))

  forward-backward : =₁ (forward ∘ backward) (id (C × (D × E)))
  forward-backward = pair-projections ∙
    (pair-cong (idIso pr₁) (pair-η pr₂) ∙
      (pair-cong backward-first
        (pair-cong backward-second backward-third ∙ pair-pre (pr₂ ∘ pr₁) pr₂ backward) ∙
        pair-pre (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂) backward))

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = invIso backward-forward
    ; retractionIso = invIso forward-backward
    }
```

The product functor is the pairing from the book. Identity and composition
are compared by their two projections, with the external associators visible.

```agda
productMap : {C C′ D D′ : CAT} → MAP C C′ → MAP D D′ → MAP (C × D) (C′ × D′)
productMap f g = pair (f ∘ pr₁) (g ∘ pr₂)

productMap-id : (C D : CAT) → =₁ (productMap (id C) (id D)) (id (C × D))
productMap-id C D = pair-projections ∙ pair-cong (comp-unitˡ pr₁) (comp-unitˡ pr₂)

productMap-comp : {C C′ C″ D D′ D″ : CAT}
  (f : MAP C C′) (f′ : MAP C′ C″) (g : MAP D D′) (g′ : MAP D′ D″)
  → =₁ (productMap f′ g′ ∘ productMap f g) (productMap (f′ ∘ f) (g′ ∘ g))
productMap-comp f f′ g g′ = pair-cong
  (invIso (comp-assoc pr₁ f f′) ∙
    ((f′ ◁ pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc (productMap f g) pr₁ f′))
  (invIso (comp-assoc pr₂ g g′) ∙
    ((g′ ◁ pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc (productMap f g) pr₂ g′))
  ∙ pair-pre (f′ ∘ pr₁) (g′ ∘ pr₂) (productMap f g)
```
