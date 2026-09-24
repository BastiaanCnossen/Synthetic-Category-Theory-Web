# Products and their functoriality

This module constructs product symmetry, units, associativity, and
functoriality. The exercises are identified by
`exercise:Functoriality_Products` and `exercise:Associativity_Products`,
independently of their placement in the book. All associators and
projection comparisons are retained.

The main declarations are `swap-isEquiv`, `product-unitʳ-isEquiv`, and the
constructions in `Associativity`. Further compatibility between these
chosen comparisons requires additional proofs; it is not part of the
individual equivalence statements below.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section03.ProductConstructions
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

```

## Reconstructing a functor from its projections

The product universal property identifies a functor with the pairing of its
projections. This is the common proof step used by the equivalences below.

```agda
pair-η : {X C D : CAT} (h : MAP X (C × D))
  → (pair (pr₁ ∘ h) (pr₂ ∘ h)) =₁ h
pair-η h = pair-iso (pair-β₁ (pr₁ ∘ h) (pr₂ ∘ h))
                        (pair-β₂ (pr₁ ∘ h) (pr₂ ∘ h))

pair-projections : {C D : CAT} → (pair pr₁ pr₂) =₁ (id (C × D))
pair-projections = pair-iso
  ((comp-unitʳ pr₁) ⁻¹ ∙ pair-β₁ pr₁ pr₂)
  ((comp-unitʳ pr₂) ⁻¹ ∙ pair-β₂ pr₁ pr₂)

project-pair₁ : {R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (r : MAP R X)
  → (pr₁ ∘ (pair f g ∘ r)) =₁ (f ∘ r)
project-pair₁ f g r = (pair-β₁ f g ▷ r) ∙ (comp-assoc r (pair f g) pr₁) ⁻¹

project-pair₂ : {R X C D : CAT}
  (f : MAP X C) (g : MAP X D) (r : MAP R X)
  → (pr₂ ∘ (pair f g ∘ r)) =₁ (g ∘ r)
project-pair₂ f g r = (pair-β₂ f g ▷ r) ∙ (comp-assoc r (pair f g) pr₂) ⁻¹
```

## Symmetry

The symmetry is its own inverse, with the categories interchanged. Its
two inverse comparisons are the same calculation on different products.

```agda
swap : {C D : CAT} → MAP (C × D) (D × C)
swap = pair pr₂ pr₁

swap-swap : (C D : CAT) → (swap ∘ swap) =₁ (id (C × D))
swap-swap C D = pair-iso
  --! begin swap-swap-first-projection
  ((comp-unitʳ pr₁) ⁻¹ ∙ (pair-β₂ pr₂ pr₁ ∙ project-pair₁ pr₂ pr₁ swap))
  --! end swap-swap-first-projection
  --! begin swap-swap-second-projection
  ((comp-unitʳ pr₂) ⁻¹ ∙ (pair-β₁ pr₂ pr₁ ∙ project-pair₂ pr₂ pr₁ swap))
  --! end swap-swap-second-projection

swap-isEquiv : (C D : CAT) → IsEquiv (swap {C} {D})
swap-isEquiv C D = record
  { inverse = swap
  ; sectionIso = (swap-swap C D) ⁻¹
  ; retractionIso = (swap-swap D C) ⁻¹
  }

```

## The right unit

The first projection `C × One → C` has inverse given by pairing the identity
with the terminal functor. The superscript `ʳ` records that the terminal
factor is on the right. We compare the two composites by their projections.

```agda
product-unitʳ-inverse : (C : CAT) → MAP C (C × One)
product-unitʳ-inverse C = pair (id C) (terminate C)

product-unitʳ-section : (C : CAT)
  → (product-unitʳ-inverse C ∘ pr₁) =₁ (id (C × One))
product-unitʳ-section C = pair-iso
  --! begin product-unit-first-projection
  ((comp-unitʳ pr₁) ⁻¹ ∙
    (comp-unitˡ pr₁ ∙ project-pair₁ (id C) (terminate C) pr₁))
  --! end product-unit-first-projection
  (terminal-iso _ _)

product-unitʳ-isEquiv : (C : CAT) → IsEquiv (pr₁ {C} {One})
product-unitʳ-isEquiv C = record
  { inverse = product-unitʳ-inverse C
  ; sectionIso = (product-unitʳ-section C) ⁻¹
  --! begin product-unit-retraction
  ; retractionIso = (pair-β₁ (id C) (terminate C)) ⁻¹
  --! end product-unit-retraction
  }
```

## Associativity

For associativity, each composite is reduced to the original three
projections and then reconstructed using `pair-η`.

```agda
module Associativity (C D E : CAT) where
  forward : MAP ((C × D) × E) (C × (D × E))
  forward = pair (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)

  backward : MAP (C × (D × E)) ((C × D) × E)
  backward = pair (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)

  forward-first : (pr₁ ∘ forward) =₁ (pr₁ ∘ pr₁)
  forward-first = pair-β₁ (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)

  forward-second : ((pr₁ ∘ pr₂) ∘ forward) =₁ (pr₂ ∘ pr₁)
  forward-second = pair-β₁ (pr₂ ∘ pr₁) pr₂ ∙
    ((pr₁ ◁ pair-β₂ (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)) ∙
      comp-assoc forward pr₂ pr₁)

  forward-third : ((pr₂ ∘ pr₂) ∘ forward) =₁ pr₂
  forward-third = pair-β₂ (pr₂ ∘ pr₁) pr₂ ∙
    ((pr₂ ◁ pair-β₂ (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)) ∙
      comp-assoc forward pr₂ pr₂)

  backward-first : ((pr₁ ∘ pr₁) ∘ backward) =₁ pr₁
  backward-first = pair-β₁ pr₁ (pr₁ ∘ pr₂) ∙
    ((pr₁ ◁ pair-β₁ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)) ∙
      comp-assoc backward pr₁ pr₁)

  backward-second : ((pr₂ ∘ pr₁) ∘ backward) =₁ (pr₁ ∘ pr₂)
  backward-second = pair-β₂ pr₁ (pr₁ ∘ pr₂) ∙
    ((pr₂ ◁ pair-β₁ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)) ∙
      comp-assoc backward pr₁ pr₂)

  backward-third : (pr₂ ∘ backward) =₁ (pr₂ ∘ pr₂)
  backward-third = pair-β₂ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)

  backward-forward : (backward ∘ forward) =₁ (id ((C × D) × E))
  backward-forward = pair-projections ∙
    (pair-cong (pair-η pr₁) (idIso pr₂) ∙
      (pair-cong
        (pair-cong forward-first forward-second ∙ pair-pre pr₁ (pr₁ ∘ pr₂) forward)
        forward-third ∙
        pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) forward))

  forward-backward : (forward ∘ backward) =₁ (id (C × (D × E)))
  forward-backward = pair-projections ∙
    (pair-cong (idIso pr₁) (pair-η pr₂) ∙
      (pair-cong backward-first
        (pair-cong backward-second backward-third ∙ pair-pre (pr₂ ∘ pr₁) pr₂ backward) ∙
        pair-pre (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂) backward))

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; sectionIso = backward-forward ⁻¹
    ; retractionIso = forward-backward ⁻¹
    }
```

## Functoriality

The product functor is the pairing from the book. Identity and composition
are compared by their two projections, with the external associators visible.

```agda
productMap : {C C′ D D′ : CAT} → MAP C C′ → MAP D D′ → MAP (C × D) (C′ × D′)
productMap f g = pair (f ∘ pr₁) (g ∘ pr₂)

productMap-id : (C D : CAT) → (productMap (id C) (id D)) =₁ (id (C × D))
productMap-id C D = pair-projections ∙ pair-cong (comp-unitˡ pr₁) (comp-unitˡ pr₂)

productMap-comp : {C C′ C″ D D′ D″ : CAT}
  (f : MAP C C′) (f′ : MAP C′ C″) (g : MAP D D′) (g′ : MAP D′ D″)
  → (productMap f′ g′ ∘ productMap f g) =₁ (productMap (f′ ∘ f) (g′ ∘ g))
productMap-comp f f′ g g′ = pair-cong
  ((comp-assoc pr₁ f f′) ⁻¹ ∙
    ((f′ ◁ pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc (productMap f g) pr₁ f′))
  ((comp-assoc pr₂ g g′) ⁻¹ ∙
    ((g′ ◁ pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc (productMap f g) pr₂ g′))
  ∙ pair-pre (f′ ∘ pr₁) (g′ ∘ pr₂) (productMap f g)
```
