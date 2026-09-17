# Commutative diagrams and the terminal span

The records below retain the comparison cells in the definitions. In
particular, comparison of span maps includes compatibility with both legs,
and a square of natural isomorphisms retains its higher cell.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section01.Specialization as Specialization

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
    cell : =₁ (right ∘ top) (bottom ∘ left)

record FunctorTriangle (C D E : CAT) : Set m where
  field
    first : MAP C D
    second : MAP D E
    diagonal : MAP C E
    cell : =₁ diagonal (second ∘ first)

record NatIsoSquare {C D : CAT} (f g f′ g′ : MAP C D) : Set m where
  field
    top : =₁ f g
    bottom : =₁ f′ g′
    left : =₁ f f′
    right : =₁ g g′
    cell : =₂ (right ∙ top) (bottom ∙ left)

record NatIsoTriangle {C D : CAT} (f g h : MAP C D) : Set m where
  field
    first : =₁ f g
    second : =₁ g h
    diagonal : =₁ f h
    cell : =₂ diagonal (second ∙ first)

record Iso₂Square {C D : CAT} {f g : MAP C D} (α β α′ β′ : =₁ f g) : Set m where
  field
    top : =₂ α β
    bottom : =₂ α′ β′
    left : =₂ α α′
    right : =₂ β β′
    cell : =₃ (right ∙ top) (bottom ∙ left)

record Span (C D : CAT) : Set (c ⊔ m) where
  field
    apex : CAT
    left : MAP apex C
    right : MAP apex D

record SpanMap {C D : CAT} (U Z : Span C D) : Set m where
  field
    functor : MAP (Span.apex U) (Span.apex Z)
    leftIso : =₁ (Span.left Z ∘ functor) (Span.left U)
    rightIso : =₁ (Span.right Z ∘ functor) (Span.right U)

record SpanMapIso {C D : CAT} {U Z : Span C D} (h k : SpanMap U Z) : Set m where
  field
    comparison : =₁ (SpanMap.functor h) (SpanMap.functor k)
    leftCompat : =₂ (SpanMap.leftIso k ∙ (Span.left Z ◁ comparison)) (SpanMap.leftIso h)
    rightCompat : =₂ (SpanMap.rightIso k ∙ (Span.right Z ◁ comparison)) (SpanMap.rightIso h)

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
      (β : =₁ g h) (α : =₁ f h) → =₂ (β ∙ (invIso β ∙ α)) α
    cancel β α = isoComp-unitˡ-at α ∙
      (isoComp-cong (isoComp-inverseʳ-at β) (idIso α)
       ∙ invIso (isoComp-assoc-at β (invIso β) α))

  productSpan-unique : {C D : CAT} {U : Span C D}
    (h k : SpanMap U (productSpan C D)) → SpanMapIso h k
  productSpan-unique h k =
    let l = invIso (SpanMap.leftIso k) ∙ SpanMap.leftIso h
        r = invIso (SpanMap.rightIso k) ∙ SpanMap.rightIso h
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
of all spans. `NatIsoSquare` also implements the varying-endpoint comparison
convention in `rmk:Isomorphisms_Of_Natural_Isomorphisms`.

General planar diagrams remain a display convention: each displayed face
retains its chosen identification. No arbitrary graph parser or global
coherence theorem is required by that convention.
