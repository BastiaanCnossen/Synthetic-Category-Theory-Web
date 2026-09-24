# Commutative diagrams and the terminal span

The records below retain the comparison cells in the definitions. In
particular, comparison of span maps includes compatibility with both legs,
while diagrams of identifications are in `Section02.Diagrams`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization

module SCT.VolumeI.Chapter01.Section01.Diagrams
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P) where

open Vocabulary V
open Operations V
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Specialization V T P PL S

record FunctorSquare (C D C′ D′ : CAT) : Set m where
  field
    top : MAP C D
    left : MAP C C′
    right : MAP D D′
    bottom : MAP C′ D′
    cell : (right ∘ top) =₁ (bottom ∘ left)

record FunctorTriangle (C D E : CAT) : Set m where
  field
    first : MAP C D
    second : MAP D E
    diagonal : MAP C E
    cell : diagonal =₁ (second ∘ first)

record Span (C D : CAT) : Set (c ⊔ m) where
  field
    apex : CAT
    left : MAP apex C
    right : MAP apex D

record SpanMap {C D : CAT} (U Z : Span C D) : Set m where
  field
    functor : MAP (Span.apex U) (Span.apex Z)
    leftIso : (Span.left Z ∘ functor) =₁ (Span.left U)
    rightIso : (Span.right Z ∘ functor) =₁ (Span.right U)

record SpanMapIso {C D : CAT} {U Z : Span C D} (h k : SpanMap U Z) : Set m where
  field
    comparison : (SpanMap.functor h) =₁ (SpanMap.functor k)
    leftCompat : (SpanMap.leftIso k ∙ (Span.left Z ◁ comparison)) =₂ (SpanMap.leftIso h)
    rightCompat : (SpanMap.rightIso k ∙ (Span.right Z ◁ comparison)) =₂ (SpanMap.rightIso h)

productSpan : (C D : CAT) → Span C D
productSpan C D = record { apex = C × D ; left = pr₁ ; right = pr₂ }

toProductSpan : {C D : CAT} (U : Span C D) → SpanMap U (productSpan C D)
toProductSpan U = record
  { functor = pair (Span.left U) (Span.right U)
  ; leftIso = pair-β₁ (Span.left U) (Span.right U)
  ; rightIso = pair-β₂ (Span.left U) (Span.right U)
  }

module Uniqueness (VC : Coherence.VerticalCoherence V T P S) where
  open Specialization.Units V T P PL S VC

  private
    cancel : {C D : CAT} {f g h : MAP C D}
      (β : g =₁ h) (α : f =₁ h) → (β ∙ (β ⁻¹ ∙ α)) =₂ α
    cancel β α = isoComp-unitˡ-at α ∙
      (isoComp-cong (isoComp-inverseʳ-at β) (idIso α)
       ∙ (isoComp-assoc-at β (β ⁻¹) α) ⁻¹)

  productSpan-unique : {C D : CAT} {U : Span C D}
    (h k : SpanMap U (productSpan C D)) → SpanMapIso h k
  productSpan-unique h k =
    let l = (SpanMap.leftIso k) ⁻¹ ∙ SpanMap.leftIso h
        r = (SpanMap.rightIso k) ⁻¹ ∙ SpanMap.rightIso h
    in record
      { comparison = pair-iso l r
      ; leftCompat = cancel (SpanMap.leftIso k) (SpanMap.leftIso h)
        ∙ isoComp-cong (idIso (SpanMap.leftIso k)) (pair-iso-β₁ l r)
      ; rightCompat = cancel (SpanMap.rightIso k) (SpanMap.rightIso h)
        ∙ isoComp-cong (idIso (SpanMap.rightIso k)) (pair-iso-β₂ l r)
      }
```

This proves the terminal-span formulation actually stated in
`rmk:Universal_Property_Product_In_Terms_Of_Spans`: maps from every span and
comparisons between any two such maps. It does not assert a synthetic category
of all spans. Diagrams with identification-valued edges are in Section 1.2.

General planar diagrams remain a display convention: each displayed face
retains its chosen identification. No arbitrary graph parser or global
coherence theorem is required by that convention.
